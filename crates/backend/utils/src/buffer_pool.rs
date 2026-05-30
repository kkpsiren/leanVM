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
use std::sync::atomic::{AtomicUsize, Ordering};
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

/// Diagnostics (set `LEAN_POOL_STATS=1`): log + tally each *big* fresh allocation (one not served
/// from the pool). Used to verify the goal — after warmup, the pool should serve every big buffer,
/// so big fresh allocations only occur when a larger size than ever before is requested.
fn stats_enabled() -> bool {
    static EN: OnceLock<bool> = OnceLock::new();
    *EN.get_or_init(|| std::env::var_os("LEAN_POOL_STATS").is_some())
}

/// Buffers at or above this many bytes count as "big" for fresh-allocation reporting.
const BIG_ALLOC_BYTES: usize = 1 << 20; // 1 MiB

static BIG_FRESH_ALLOCS: AtomicUsize = AtomicUsize::new(0);

#[cold]
fn record_fresh_alloc<T>(min_cap: usize) {
    let bytes = min_cap.saturating_mul(size_of::<T>());
    if bytes >= BIG_ALLOC_BYTES {
        let n = BIG_FRESH_ALLOCS.fetch_add(1, Ordering::Relaxed) + 1;
        eprintln!(
            "[pool] big fresh alloc #{n}: {} MiB  ({min_cap} x {})",
            bytes >> 20,
            std::any::type_name::<T>()
        );
    }
}

/// Total number of big fresh allocations so far (snapshot across proofs to check it stops growing).
#[must_use]
pub fn big_fresh_alloc_count() -> usize {
    BIG_FRESH_ALLOCS.load(Ordering::Relaxed)
}

static GLOBAL_BIG_ALLOCS: AtomicUsize = AtomicUsize::new(0);
// Histogram of big allocations by `floor(log2(size))` (indices ~20..40 = 1 MiB .. 1 TiB).
static SIZE_HIST: [AtomicUsize; 48] = [const { AtomicUsize::new(0) }; 48];

#[inline]
fn record_global_alloc(size: usize) {
    if size >= BIG_ALLOC_BYTES {
        GLOBAL_BIG_ALLOCS.fetch_add(1, Ordering::Relaxed);
        let bucket = (usize::BITS - 1 - size.leading_zeros()) as usize;
        SIZE_HIST[bucket.min(47)].fetch_add(1, Ordering::Relaxed);
    }
}

/// A `#[global_allocator]` wrapper (used behind the binary's `count-allocs` feature) that tallies
/// every process-wide allocation `>= BIG_ALLOC_BYTES`, delegating to the system allocator. It
/// catches *all* big allocations — pooled or not — so one can verify that after warmup the prover
/// makes essentially no fresh big allocations (compare the total at `--repeat 1` vs `--repeat N`).
/// The atomic counters never allocate, so this is safe to call from inside the allocator.
#[derive(Debug, Default, Clone, Copy)]
pub struct CountingSystemAlloc;

unsafe impl std::alloc::GlobalAlloc for CountingSystemAlloc {
    unsafe fn alloc(&self, layout: std::alloc::Layout) -> *mut u8 {
        record_global_alloc(layout.size());
        unsafe { std::alloc::System.alloc(layout) }
    }
    unsafe fn dealloc(&self, ptr: *mut u8, layout: std::alloc::Layout) {
        unsafe { std::alloc::System.dealloc(ptr, layout) };
    }
    unsafe fn alloc_zeroed(&self, layout: std::alloc::Layout) -> *mut u8 {
        record_global_alloc(layout.size());
        unsafe { std::alloc::System.alloc_zeroed(layout) }
    }
    unsafe fn realloc(&self, ptr: *mut u8, layout: std::alloc::Layout, new_size: usize) -> *mut u8 {
        if new_size > layout.size() {
            record_global_alloc(new_size);
        }
        unsafe { std::alloc::System.realloc(ptr, layout, new_size) }
    }
}

/// Process-wide count of allocations `>= BIG_ALLOC_BYTES` (meaningful only under the `count-allocs`
/// build, where [`CountingSystemAlloc`] is installed as the global allocator).
#[must_use]
pub fn global_big_alloc_count() -> usize {
    GLOBAL_BIG_ALLOCS.load(Ordering::Relaxed)
}

/// Print the big-allocation size histogram (counts per power-of-two size bucket) to stderr.
pub fn print_alloc_histogram() {
    eprintln!("[count-allocs] big (>=1 MiB) allocation size histogram:");
    for (b, c) in SIZE_HIST.iter().enumerate() {
        let n = c.load(Ordering::Relaxed);
        if n > 0 {
            let lo = 1usize << b;
            let unit = if b >= 30 { (lo >> 30, "GiB") } else { (lo >> 20, "MiB") };
            eprintln!("  [{:>4} {}, {:>4} {}): {n}", unit.0, unit.1, unit.0 * 2, unit.1);
        }
    }
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
    // Best-fit (smallest capacity `>= min_cap`): a small request must not consume a large pooled
    // buffer, or the next large request would have to allocate fresh ("small-grabs-big").
    let best = list
        .iter()
        .enumerate()
        .filter(|(_, b)| b.capacity() >= min_cap)
        .min_by_key(|(_, b)| b.capacity())
        .map(|(i, _)| i);
    if let Some(pos) = best {
        list.swap_remove(pos) // already `len == 0` (cleared on checkin)
    } else {
        drop(list);
        if stats_enabled() {
            record_fresh_alloc::<T>(min_cap);
        }
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
