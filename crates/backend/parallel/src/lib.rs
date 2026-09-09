//! Shared range combinators with a serial dispatcher on raw Wasm.
#[cfg(not(target_arch = "wasm32"))]
mod threaded;
#[cfg(not(target_arch = "wasm32"))]
pub use threaded::*;
#[cfg(not(target_arch = "wasm32"))]
use threaded::current_worker_id;
#[cfg(target_arch = "wasm32")]
mod serial;
#[cfg(target_arch = "wasm32")]
pub use serial::*;
#[cfg(target_arch = "wasm32")]
use serial::current_worker_id;

/// `f(i)` for every `i` in `0..n_tasks`, in parallel. `#[inline]` folds the range→index adapter
/// into the monomorphized [`for_each_chunk`].
#[inline]
pub fn for_each_index<F: Fn(usize) + Sync>(n_tasks: usize, f: F) {
    for_each_chunk(n_tasks, |start, end| {
        for i in start..end {
            f(i);
        }
    });
}

/// A base `*mut` shareable across workers. Sound only because callers partition the allocation
/// by task index (disjoint regions).
#[derive(Debug)]
pub struct SendPtr<T>(pub *mut T);
// SAFETY: accesses are partitioned by task index (see callers).
unsafe impl<T> Send for SendPtr<T> {}
unsafe impl<T> Sync for SendPtr<T> {}

impl<T> SendPtr<T> {
    /// Offset the base by `n` elements.
    /// # Safety
    /// `n` stays in the allocation; any write targets a slot no concurrent task touches.
    #[inline]
    pub unsafe fn add(&self, n: usize) -> *mut T {
        unsafe { self.0.add(n) }
    }

    /// Reconstruct the `len`-element slice at element offset `off`.
    /// # Safety
    /// `off`/`len` in-bounds and disjoint from every other concurrent task's slice.
    #[inline]
    pub unsafe fn slice<'a>(&self, off: usize, len: usize) -> &'a mut [T] {
        unsafe { std::slice::from_raw_parts_mut(self.0.add(off), len) }
    }
}

/// Parallel `data.chunks_mut(chunk).enumerate().for_each(f)`; the final chunk may be shorter.
pub fn par_chunks_mut<T: Send, F>(data: &mut [T], chunk: usize, f: F)
where
    F: Fn(usize, &mut [T]) + Sync,
{
    assert!(chunk > 0, "chunk size must be non-zero");
    let len = data.len();
    let base = SendPtr(data.as_mut_ptr());
    for_each_index(len.div_ceil(chunk), |i| {
        let start = i * chunk;
        // SAFETY: distinct `i` give disjoint in-bounds ranges; `data` stays borrowed.
        let slice = unsafe { base.slice(start, chunk.min(len - start)) };
        f(i, slice);
    });
}

/// Parallel `data.iter_mut().enumerate().for_each(f)`, chunked by [`recommended_chunk_size`].
/// Hands the closure each element's **global** index. `#[inline]` folds the per-chunk adapter
/// into the monomorphized [`par_chunks_mut`].
#[inline]
pub fn par_for_each_mut<T: Send, F>(data: &mut [T], f: F)
where
    F: Fn(usize, &mut T) + Sync,
{
    let chunk = recommended_chunk_size(data.len());
    par_chunks_mut(data, chunk, |ci, sub| {
        for (k, slot) in sub.iter_mut().enumerate() {
            f(ci * chunk + k, slot);
        }
    });
}

/// [`par_for_each_mut`] over two equal-length slices at once: `f(i, &mut a[i], &mut b[i])`
#[inline]
pub fn par_for_each_mut2<A: Send, B: Send, F>(a: &mut [A], b: &mut [B], f: F)
where
    F: Fn(usize, &mut A, &mut B) + Sync,
{
    assert_eq!(a.len(), b.len(), "par_for_each_mut2: slices differ in length");
    let bp = SendPtr(b.as_mut_ptr());
    par_for_each_mut(a, |i, ai| {
        f(i, ai, unsafe { &mut *bp.add(i) });
    });
}

/// Parallel `(0..n_tasks).map(f).collect::<Vec<_>>()`: runs `f(i)` across the pool and writes each
/// result straight into the output in index order — one allocation, no `Option` slots.
pub fn par_map_collect<T: Send, F: Fn(usize) -> T + Sync>(n_tasks: usize, f: F) -> Vec<T> {
    let mut out: Vec<T> = Vec::with_capacity(n_tasks);
    let base = SendPtr(out.as_mut_ptr());
    for_each_index(n_tasks, |i| {
        // SAFETY: distinct `i` write disjoint, in-bounds slots (each exactly once) and the
        // dispatch blocks until all writes finish. A panic in `f` leaks the slots written so
        // far, which is fine: a pool task panic is fatal (see the module's "Panics" note).
        unsafe { base.add(i).write(f(i)) };
    });
    // SAFETY: every slot in `0..n_tasks` was initialized exactly once above.
    unsafe { out.set_len(n_tasks) };
    out
}

/// Parallel `for (i, slot) in dst.iter_mut().enumerate() { *slot = build(i); }`: fill an existing
/// slice from an index closure. The in-place dual of [`par_map_collect`] (which allocates).
/// `#[inline]` folds the fill adapter into the monomorphized [`par_for_each_mut`]. Always
/// dispatches to the pool; guard the call yourself when small inputs need a sequential fast path.
#[inline]
pub fn par_fill<T: Send, F: Fn(usize) -> T + Sync>(dst: &mut [T], build: F) {
    par_for_each_mut(dst, |i, slot| *slot = build(i));
}

/// Give each worker its own persistent `Option<S>` slot while it drains `0..n_tasks`:
/// `run(slot, start, end)` fires once per claimed batch with that worker's slot, so state
/// accumulates across its batches. Returns the slots (rest `None`) for the caller to combine.
fn drain_into_slots<S: Send>(n_tasks: usize, run: impl Fn(&mut Option<S>, usize, usize) + Sync) -> Vec<Option<S>> {
    let mut slots: Vec<Option<S>> = (0..num_threads()).map(|_| None).collect();
    let ptr = SendPtr(slots.as_mut_ptr());
    for_each_chunk(n_tasks, |start, end| {
        // SAFETY: `current_worker_id() < NUM_THREADS` is unique per live worker → disjoint
        // slots; `slots` outlives the dispatch.
        let slot = unsafe { &mut *ptr.add(current_worker_id()) };
        run(slot, start, end);
    });
    slots
}

/// Parallel map-reduce over `0..n_tasks` = `(0..n).map(map).reduce(identity, reduce)`. Each
/// worker folds its claimed indices into one local partial; the partials combine on the
/// dispatcher. `reduce` must be associative with `identity()` a neutral element.
pub fn map_reduce<T, ID, M, R>(n_tasks: usize, identity: ID, map: M, reduce: R) -> T
where
    T: Send,
    ID: Fn() -> T,
    M: Fn(usize) -> T + Sync,
    R: Fn(T, T) -> T + Sync,
{
    let slots = drain_into_slots(n_tasks, |slot, start, end| {
        // Fold the batch into the worker's partial, seeded by the first `map` so `identity`
        // stays off the per-element path; take/replace the shared slot just once.
        *slot = (start..end).fold(slot.take(), |acc, i| {
            Some(acc.map_or_else(|| map(i), |a| reduce(a, map(i))))
        });
    });
    // `identity()` seeds the combine as a no-op left-identity; the empty and single-thread
    // (`for_each_chunk` runs inline) cases then fall out without a special path.
    slots.into_iter().flatten().fold(identity(), &reduce)
}

/// Parallel reduce where each worker keeps reusable scratch beside its accumulator (so the
/// per-task body needn't allocate). `(scratch, acc)` are created once per worker and threaded
/// through its batches; the `acc`s combine on the dispatcher. `combine` must be associative
/// with `init_acc()` a neutral element.
pub fn map_reduce_with_state<S, A, IS, IA, F, C>(n_tasks: usize, init_state: IS, init_acc: IA, fold: F, combine: C) -> A
where
    S: Send,
    A: Send,
    IS: Fn() -> S + Sync,
    IA: Fn() -> A + Sync,
    F: Fn(&mut S, &mut A, usize) + Sync,
    C: Fn(A, A) -> A,
{
    let slots = drain_into_slots(n_tasks, |slot, start, end| {
        let (state, acc) = slot.get_or_insert_with(|| (init_state(), init_acc()));
        for i in start..end {
            fold(state, acc, i);
        }
    });
    // `init_acc()` seeds the combine as a neutral element; the empty and single-thread cases
    // (`for_each_chunk` runs inline) then fall out without a special path.
    slots
        .into_iter()
        .flatten()
        .map(|(_, acc)| acc)
        .fold(init_acc(), &combine)
}
