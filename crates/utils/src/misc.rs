use std::sync::atomic::{AtomicPtr, Ordering};

use backend::*;

pub fn from_end<A>(slice: &[A], n: usize) -> &[A] {
    assert!(n <= slice.len());
    &slice[slice.len() - n..]
}

pub fn transposed_par_iter_mut<A: Send + Sync, const N: usize>(
    array: &mut [Vec<A>; N], // all vectors must have the same length
) -> impl IndexedParallelIterator<Item = [&mut A; N]> + '_ {
    let len = array[0].len();
    let data_ptrs: [AtomicPtr<A>; N] = array.each_mut().map(|v| AtomicPtr::new(v.as_mut_ptr()));

    (0..len)
        .into_par_iter()
        .map(move |i| unsafe { std::array::from_fn(|j| &mut *data_ptrs[j].load(Ordering::Relaxed).add(i)) })
}

/// Like [`transposed_par_iter_mut`], but over a single flat **column-major** buffer
/// (`data[c * n_rows + r]`) rather than `[Vec<A>; N]`. Yields, for each of the first
/// `n_active` rows, the array of `N` mutable references to that row's cells. Used to build a
/// table trace row-by-row directly into its final flat storage.
pub fn transposed_par_iter_mut_flat<A: Send + Sync, const N: usize>(
    data: &mut [A],
    n_rows: usize,
    n_active: usize,
) -> impl IndexedParallelIterator<Item = [&mut A; N]> + '_ {
    assert!(data.len() >= N * n_rows);
    assert!(n_active <= n_rows);
    let base = data.as_mut_ptr();
    let col_ptrs: [AtomicPtr<A>; N] = std::array::from_fn(|c| AtomicPtr::new(unsafe { base.add(c * n_rows) }));

    (0..n_active)
        .into_par_iter()
        .map(move |i| unsafe { std::array::from_fn(|c| &mut *col_ptrs[c].load(Ordering::Relaxed).add(i)) })
}

pub fn collect_refs<T>(vecs: &[Vec<T>]) -> Vec<&[T]> {
    vecs.iter().map(Vec::as_slice).collect()
}

#[derive(Debug, Clone, Default)]
pub struct Counter(usize);

impl Counter {
    pub fn get_next(&mut self) -> usize {
        let val = self.0;
        self.0 += 1;
        val
    }

    pub fn new() -> Self {
        Self(0)
    }
}
