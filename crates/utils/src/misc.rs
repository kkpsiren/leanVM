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

pub fn collect_refs<T>(vecs: &[Vec<T>]) -> Vec<&[T]> {
    vecs.iter().map(Vec::as_slice).collect()
}

/// Interior-mutability counter so the compiler can hand out `&Counter`s to
/// parallel workers (e.g. parallel match-arm transforms in `a_simplify_lang`)
/// without forcing them to serialize on a `&mut`. The IDs handed out are still
/// unique across threads — relaxed atomic increment is enough since the only
/// requirement is "no two get_next calls return the same value".
#[derive(Debug, Default)]
pub struct Counter(std::sync::atomic::AtomicUsize);

impl Clone for Counter {
    fn clone(&self) -> Self {
        Self(std::sync::atomic::AtomicUsize::new(
            self.0.load(std::sync::atomic::Ordering::Relaxed),
        ))
    }
}

impl Counter {
    pub fn get_next(&self) -> usize {
        self.0.fetch_add(1, std::sync::atomic::Ordering::Relaxed)
    }

    pub fn new() -> Self {
        Self(std::sync::atomic::AtomicUsize::new(0))
    }
}
