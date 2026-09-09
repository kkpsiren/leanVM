//! Minimal fixed-size thread pool for flat data-parallel kernels ("split a range, run a closure
//! on each piece"). No work-stealing, no per-dispatch allocation; owning the runtime lets us pin
//! per-worker scratch and drop rayon.
//!
//! - **Model.** `NUM_THREADS-1` background workers (ids `1..NUM_THREADS`); the dispatcher is
//!   worker 0 and runs its share inline. Workers claim ranges from a shared atomic counter
//!   (guided self-scheduling) for load balance.
//! - **Lock-free dispatch.** Dispatch bumps a `generation` counter idle workers spin on, parking
//!   after `SPIN_LIMIT` spins; completion is a `working` countdown the dispatcher spins on.
//!   `parked` is SeqCst-ordered against `generation`, so each dispatch one side sees the other
//!   (no lost wakeup) and unpark is skipped while a worker spins.
//! - **No nesting.** A dispatch from within a task would deadlock the dispatch lock; an `IN_TASK`
//!   guard panics instead.
//! - **Panics.** A task panic is caught on its worker and re-raised on the dispatcher once the
//!   dispatch quiesces; the pool stays usable.
//! - **One dispatcher at a time**, serialized by the `dispatch` mutex.

use std::any::Any;
use std::cell::{Cell, UnsafeCell};
use std::marker::PhantomData;
use std::panic::{AssertUnwindSafe, catch_unwind, resume_unwind};
use std::ptr::NonNull;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Mutex, Once, OnceLock};
use std::thread::Thread;

/// Idle spins before a worker parks: long enough to stay hot across back-to-back dispatches,
/// short enough to yield the core during sequential gaps.
const SPIN_LIMIT: u32 = 1 << 12;

/// Max tasks claimed in one guided-self-scheduling step: bounds load imbalance while keeping
/// million-task kernels to a few thousand claims.
const MAX_CLAIM_BATCH: usize = 1 << 12;

/// Worker count including the dispatcher. Resolved once at runtime (see [`system_info::num_threads`]).
#[must_use]
pub fn num_threads() -> usize {
    system_info::num_threads()
}

/// Chunk size for a flat fan-out: a few chunks per worker — fine enough for the counter to
/// rebalance heterogeneous cores, coarse enough to amortize dispatch.
#[must_use]
#[inline]
pub fn recommended_chunk_size(n_items: usize) -> usize {
    n_items.div_ceil(num_threads() * 4).max(1)
}

thread_local! {
    /// Stable pool id of this thread; `0` on the dispatcher and off-pool threads.
    static WORKER_ID: Cell<usize> = const { Cell::new(0) };
    /// Set while running a task; a dispatch in this state is forbidden nesting (panics).
    static IN_TASK: Cell<bool> = const { Cell::new(false) };
    /// Set by `forbid_parallelism` (`forbid-parallelism` feature): pool dispatch on this thread panics while set.
    static FORBIDDEN: Cell<bool> = const { Cell::new(false) };
}

/// Calling worker's id in `0..NUM_THREADS` (`0` off-pool).
#[must_use]
pub(crate) fn current_worker_id() -> usize {
    WORKER_ID.with(Cell::get)
}

/// True while the calling thread is running a pool task, where a nested dispatch would panic.
/// Lets code that runs both from the dispatcher and from within tasks pick a sequential path.
#[must_use]
pub fn is_in_pool_task() -> bool {
    IN_TASK.get()
}

/// Forbid pool dispatch on this thread until the guard drops; `zk-alloc` extends the ban to
/// arena allocation.
#[must_use]
pub fn forbid_parallelism() -> ForbidParallelismGuard {
    ForbidParallelismGuard {
        prev: cfg!(feature = "forbid-parallelism") && FORBIDDEN.replace(true),
        _not_send: PhantomData,
    }
}

#[must_use]
#[inline]
pub fn parallelism_forbidden() -> bool {
    cfg!(feature = "forbid-parallelism") && FORBIDDEN.get()
}

#[derive(Debug)]
pub struct ForbidParallelismGuard {
    prev: bool,
    _not_send: PhantomData<*const ()>,
}

impl Drop for ForbidParallelismGuard {
    fn drop(&mut self) {
        if cfg!(feature = "forbid-parallelism") {
            FORBIDDEN.set(self.prev);
        }
    }
}

/// Type-erased work unit. The `&dyn Fn` lifetime is erased to `'static`; it is dereferenced
/// only inside a dispatch window during which the dispatcher blocks, so the borrow outlives
/// every call. Range-based (`f(start, end)`) so a reduction looks up its per-worker
/// accumulator once per claimed batch, not per element.
struct Job {
    f: NonNull<dyn Fn(usize, usize) + Sync>,
    n_tasks: usize,
}

/// Park/unpark state, indexed by worker id (slot 0, the dispatcher, never parks).
#[derive(Debug)]
struct Worker {
    /// "Currently parked", SeqCst-ordered against `Pool::generation`.
    parked: AtomicBool,
    /// Handle for `unpark`, published once at worker start-up.
    handle: OnceLock<Thread>,
}

struct Pool {
    /// Current job: written by the dispatcher before the `generation` bump, read by workers
    /// after observing it (the bump supplies the happens-before).
    job: UnsafeCell<Option<Job>>,
    /// Bumped once per dispatch; idle workers watch it (spin, then park).
    generation: AtomicUsize,
    /// Next task index to claim; reset to 0 per dispatch.
    counter: AtomicUsize,
    /// Background workers still draining; the dispatcher spins this to 0.
    working: AtomicUsize,
    /// Park flag + unpark handle per worker (slot 0 unused).
    workers: Vec<Worker>,
    /// Serializes dispatchers: one driver at a time.
    dispatch: Mutex<()>,
    /// First task-panic payload of the current dispatch, re-raised by the dispatcher. Caught
    /// here so it can't unwind across `worker_main` (which would skip the `working` decrement
    /// and deadlock the completion spin).
    panic: Mutex<Option<Box<dyn Any + Send>>>,
}

// SAFETY: `job` is written only by the sole dispatcher (while workers are parked or before
// they observe the generation bump) and read only after; the generation release/acquire and
// SeqCst park protocol order the phases. The erased `Job` pointer is used only within a
// dispatch window where its borrow is live.
unsafe impl Sync for Pool {}
unsafe impl Send for Pool {}

/// Idempotent warm-up: spawn workers and run one empty dispatch so the pool and the (macOS)
/// lazily-allocated mutex exist before timed work; otherwise the pool inits on first use.
pub fn init() {
    static INIT: Once = Once::new();
    INIT.call_once(|| {
        let _ = pool();
        if num_threads() > 1 {
            for_each_index(num_threads(), |_| {});
        }
    });
}

fn pool() -> &'static Pool {
    static POOL: OnceLock<&'static Pool> = OnceLock::new();
    POOL.get_or_init(|| {
        let n = num_threads().max(1);
        let p: &'static Pool = Box::leak(Box::new(Pool {
            job: UnsafeCell::new(None),
            generation: AtomicUsize::new(0),
            counter: AtomicUsize::new(0),
            working: AtomicUsize::new(0),
            workers: (0..n)
                .map(|_| Worker {
                    parked: AtomicBool::new(false),
                    handle: OnceLock::new(),
                })
                .collect(),
            dispatch: Mutex::new(()),
            panic: Mutex::new(None),
        }));
        for id in 1..n {
            std::thread::Builder::new()
                .name(format!("parallel-worker-{id}"))
                .spawn(move || worker_main(p, id))
                .expect("failed to spawn pool worker");
        }
        p
    })
}

fn worker_main(pool: &'static Pool, id: usize) {
    WORKER_ID.with(|c| c.set(id));
    let _ = pool.workers[id].handle.set(std::thread::current());
    // Leaked, lives for the whole process; workers never shut down. One iteration per dispatch.
    let mut last_gen = 0usize;
    loop {
        last_gen = wait_for_dispatch(pool, id, last_gen);
        drain(pool);
        pool.working.fetch_sub(1, Ordering::Release);
    }
}

/// Block until a new job is published, returning its generation. Spins up to [`SPIN_LIMIT`], then
/// parks: publish `parked = true`, re-check `generation`, both SeqCst — the same total order the
/// dispatcher's bump and `parked` load observe, so a wakeup can't be lost.
fn wait_for_dispatch(pool: &Pool, id: usize, last_gen: usize) -> usize {
    let mut spins = 0u32;
    loop {
        let g = pool.generation.load(Ordering::Acquire);
        if g != last_gen {
            return g;
        }
        if spins < SPIN_LIMIT {
            spins += 1;
            std::hint::spin_loop();
            continue;
        }
        // Announce intent to park, then re-check: park only if nothing changed, else re-loop.
        pool.workers[id].parked.store(true, Ordering::SeqCst);
        if pool.generation.load(Ordering::SeqCst) == last_gen {
            std::thread::park();
        }
        pool.workers[id].parked.store(false, Ordering::SeqCst);
        spins = 0;
    }
}

/// Claim and run task ranges until the counter is exhausted (guided self-scheduling: each claim
/// takes `remaining / (NUM_THREADS*2)`, clamped to `1..=`[`MAX_CLAIM_BATCH`]). Big early claims
/// cut counter contention; the proportional shrink keeps the tail balanced.
fn drain(pool: &Pool) {
    // SAFETY: the dispatcher published `Some(job)` before the bump this worker observed and
    // overwrites it only on the next dispatch (gated on `working == 0`); no writer during drain.
    let job = unsafe { (*pool.job.get()).as_ref().expect("drain without a published job") };
    // SAFETY: `job.f` borrows a `&dyn Fn` the blocked dispatcher keeps live.
    let f = unsafe { job.f.as_ref() };
    let n = job.n_tasks;
    let nt = num_threads();
    let prev = IN_TASK.replace(true); // catch nested dispatch (see `for_each_chunk`)
    // Catch a task panic so it can't unwind across `worker_main` (skipping the `working`
    // decrement → deadlock) or poison the dispatch lock; `for_each_chunk` re-raises it.
    let result = catch_unwind(AssertUnwindSafe(|| {
        loop {
            // Stale read only affects granularity: `fetch_add` tiles `0..n` into disjoint claims.
            let observed = pool.counter.load(Ordering::Relaxed);
            if observed >= n {
                break;
            }
            let batch = ((n - observed) / (nt * 2)).clamp(1, MAX_CLAIM_BATCH);
            let start = pool.counter.fetch_add(batch, Ordering::Relaxed);
            if start >= n {
                break;
            }
            f(start, (start + batch).min(n));
        }
    }));
    IN_TASK.set(prev);
    if let Err(payload) = result {
        pool.panic.lock().unwrap().get_or_insert(payload); // keep the first
    }
}

/// Run `f(start, end)` over disjoint ranges tiling `0..n_tasks`, in parallel; a worker may get
/// several (guided self-scheduling, see [`drain`]). Blocks until done, the dispatcher acting as
/// worker 0. The base primitive — range-based so reductions amortize per-worker lookups.
pub fn for_each_chunk<F: Fn(usize, usize) + Sync>(n_tasks: usize, f: F) {
    assert!(!parallelism_forbidden(), "pool dispatch while parallelism is forbidden");
    // Nesting would deadlock the dispatch lock — panic so it's caught, not silently serial.
    assert!(!IN_TASK.get(), "nested parallel dispatch from within a pool task");

    // Trivial sizes / single-core builds run inline.
    let nt = num_threads();
    if nt <= 1 || n_tasks <= 1 {
        if n_tasks > 0 {
            f(0, n_tasks);
        }
        return;
    }

    let pool = pool();
    let _guard = pool.dispatch.lock().unwrap();

    // SAFETY: erase the borrow to `'static` so it fits the `Job`. The dispatcher blocks on
    // `working` before returning, so `f` outlives every deref. `transmute` (not a `*const dyn`
    // cast) is required: a bare cast would default the trait object to `'static` and force
    // `F: 'static` (E0310); the transmute reinterprets the same fat pointer without that bound.
    let f_ref: &(dyn Fn(usize, usize) + Sync) = &f;
    let f_erased: NonNull<dyn Fn(usize, usize) + Sync> = unsafe { std::mem::transmute(NonNull::from(f_ref)) };

    // SAFETY: sole writer — prior dispatch fully drained (`working == 0`), next not yet observed.
    unsafe { *pool.job.get() = Some(Job { f: f_erased, n_tasks }) };
    pool.counter.store(0, Ordering::Relaxed);
    pool.working.store(nt - 1, Ordering::Release);
    pool.generation.fetch_add(1, Ordering::SeqCst); // publish; SeqCst guards the park protocol

    // Wake only parked workers; spinning ones see the bump for free.
    for worker in &pool.workers[1..] {
        if worker.parked.load(Ordering::SeqCst)
            && let Some(t) = worker.handle.get()
        {
            t.unpark();
        }
    }

    drain(pool); // dispatcher runs as worker 0
    while pool.working.load(Ordering::Acquire) != 0 {
        std::hint::spin_loop(); // lock-free completion wait
    }

    // Re-raise the first task panic (if any) after dropping `_guard`, so the lock releases
    // cleanly (no poison) and the pool stays usable.
    let panicked = pool.panic.lock().unwrap().take();
    drop(_guard);
    if let Some(payload) = panicked {
        resume_unwind(payload);
    }
}


use crate::for_each_index;
