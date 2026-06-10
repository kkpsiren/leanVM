// Credits: Plonky3 (https://github.com/Plonky3/Plonky3) (MIT and Apache-2.0 licenses).

use field::{Algebra, InjectiveMonomial};
use goldilocks::{Goldilocks, Poseidon1Goldilocks8};

pub trait Compression<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn compress(&self, mut input: T) -> T {
        self.compress_mut(&mut input);
        input
    }

    fn compress_mut(&self, input: &mut T);
}

impl<R: Algebra<Goldilocks> + InjectiveMonomial<7> + Copy + Send + Sync + 'static> Compression<[R; 8]>
    for Poseidon1Goldilocks8
{
    fn compress_mut(&self, input: &mut [R; 8]) {
        self.compress_in_place(input);
    }
}

/// A permutation in the mathematical sense.
pub trait Permutation<T: Clone>: Clone + Sync {
    #[inline(always)]
    fn permute(&self, mut input: T) -> T {
        self.permute_mut(&mut input);
        input
    }

    fn permute_mut(&self, input: &mut T);
}

impl<R: Algebra<Goldilocks> + InjectiveMonomial<7> + Copy + Send + Sync + 'static> Permutation<[R; 8]>
    for Poseidon1Goldilocks8
{
    fn permute_mut(&self, input: &mut [R; 8]) {
        self.permute_in_place(input);
    }
}
