//! Process-global free-lists of large `Vec<T>` buffers, reused across proofs.
//!
//! The prover allocates and frees gigabytes of large buffers per proof. With the system allocator,
//! freeing a large block returns its pages to the OS, so the next proof re-faults them — a ~27%
//! penalty on the aggregation benchmark. Allocator-level retention (glibc `M_TRIM_THRESHOLD=-1` /
//! `M_MMAP_MAX=0`, configured by the binary) avoids the re-fault implicitly; this pool does the
//! same thing *explicitly* for the largest buffers, which additionally gives them deterministic
//! addresses across proofs (steadier cache/TLB behavior) and removes them from the allocator's
//! bookkeeping entirely. It lives in `mt-utils` (the lowest crate) so every layer — VM trace,
//! logup/GKR, WHIR, sumcheck — can return its big buffers here.
//!
//! There is one free-list per element type (`F`, `EF`, packed variants, …), keyed by [`TypeId`].
//!
//! Checkout/return happen at proof granularity (a handful of times per proof), never in a hot
//! loop, so the locks are effectively uncontended: top-level proofs run sequentially, and tests
//! that prove on parallel threads only serialize briefly here.
//!
//! A checked-out buffer comes back with **stale contents** from a prior proof. Reuse is sound only
//! if the caller writes every element before reading it: `resize(n, ZERO)` (or another full fill)
//! when the algorithm relies on zero-initialization, or `set_len(n)` + a full overwrite otherwise.

use std::any::{Any, TypeId};
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};

/// `TypeId` → that type's free-list, type-erased. Exactly one `TypeId` maps to one concrete `T`,
/// so the stored value is always `Arc<Mutex<Vec<Vec<T>>>>` for that `T`.
type Registry = Mutex<HashMap<TypeId, Box<dyn Any + Send>>>;

fn registry() -> &'static Registry {
    static REG: OnceLock<Registry> = OnceLock::new();
    REG.get_or_init(|| Mutex::new(HashMap::new()))
}

fn pool_for<T: Send + 'static>() -> Arc<Mutex<Vec<Vec<T>>>> {
    let mut reg = registry().lock().unwrap();
    reg.entry(TypeId::of::<T>())
        .or_insert_with(|| Box::new(Arc::new(Mutex::new(Vec::<Vec<T>>::new()))) as Box<dyn Any + Send>)
        .downcast_ref::<Arc<Mutex<Vec<Vec<T>>>>>()
        .expect("one TypeId maps to exactly one concrete element type")
        .clone()
}

/// Escape hatch for A/B measurement: set `LEAN_NO_POOL=1` to bypass the pool entirely (every
/// checkout allocates fresh, every checkin frees), so the pool's effect can be measured in one
/// session without rebuilding.
fn disabled() -> bool {
    static DISABLED: OnceLock<bool> = OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("LEAN_NO_POOL").is_some())
}

/// Take a `Vec<T>` with capacity `>= min_cap` from the pool (reusing already-faulted pages), or
/// allocate a fresh one if none fits. Returned with `len == 0`; the caller must fill it before
/// reading. First-fit, since each free-list holds only a handful of similarly-sized large buffers.
#[must_use]
pub fn checkout_t<T: Send + 'static>(min_cap: usize) -> Vec<T> {
    if disabled() {
        return Vec::with_capacity(min_cap);
    }
    let pool = pool_for::<T>();
    let mut list = pool.lock().unwrap();
    if let Some(pos) = list.iter().position(|b| b.capacity() >= min_cap) {
        list.swap_remove(pos) // already `len == 0` (cleared on checkin)
    } else {
        drop(list);
        Vec::with_capacity(min_cap)
    }
}

/// Return a `Vec<T>` to its free-list for a later proof to reuse. Empty buffers (no allocation) are
/// dropped rather than retained.
pub fn checkin_t<T: Send + 'static>(mut buf: Vec<T>) {
    if disabled() || buf.capacity() == 0 {
        return;
    }
    buf.clear();
    pool_for::<T>().lock().unwrap().push(buf);
}
