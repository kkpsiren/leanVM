//! A process-global free-list of large `Vec<F>` buffers, reused across proofs.
//!
//! The prover allocates and frees gigabytes of large buffers per proof. With the system allocator,
//! freeing a large block returns its pages to the OS, so the next proof re-faults them — the
//! ~27% penalty that motivated retaining freed memory in the first place (see
//! `lean_multisig::tune_allocator`). Allocator-level retention (glibc `M_TRIM_THRESHOLD=-1` /
//! `M_MMAP_MAX=0`) avoids the re-fault implicitly; this pool does the same thing *explicitly* for
//! the few largest buffers, which additionally gives them deterministic
//! addresses across proofs (steadier cache/TLB behavior) and removes them from the allocator's
//! bookkeeping entirely.
//!
//! Checkout/return happen at proof granularity (a handful of times per proof), never in a hot
//! loop, so the single `Mutex` is effectively uncontended: top-level proofs run sequentially, and
//! tests that prove on parallel threads only serialize briefly here.

use crate::F;
use std::sync::{Mutex, OnceLock};

static POOL: Mutex<Vec<Vec<F>>> = Mutex::new(Vec::new());

/// Escape hatch for A/B measurement: set `LEAN_NO_POOL=1` to bypass the pool entirely (every
/// checkout allocates fresh, every checkin frees), so the pool's effect can be measured in one
/// session without rebuilding.
fn disabled() -> bool {
    static DISABLED: OnceLock<bool> = OnceLock::new();
    *DISABLED.get_or_init(|| std::env::var_os("LEAN_NO_POOL").is_some())
}

/// Take a buffer with capacity `>= min_cap` from the pool (reusing already-faulted pages), or
/// allocate a fresh one if none fits. Returned with `len == 0`; the caller must fill it before
/// reading. First-fit, since the pool holds only a handful of similarly-sized large buffers.
#[must_use]
pub fn checkout(min_cap: usize) -> Vec<F> {
    if disabled() {
        return Vec::with_capacity(min_cap);
    }
    let mut pool = POOL.lock().unwrap();
    if let Some(pos) = pool.iter().position(|b| b.capacity() >= min_cap) {
        let mut buf = pool.swap_remove(pos);
        buf.clear();
        buf
    } else {
        drop(pool);
        Vec::with_capacity(min_cap)
    }
}

/// Return a buffer to the pool for a later proof to reuse. Empty buffers (no allocation) are
/// dropped rather than retained.
pub fn checkin(mut buf: Vec<F>) {
    if disabled() || buf.capacity() == 0 {
        return;
    }
    buf.clear();
    POOL.lock().unwrap().push(buf);
}
