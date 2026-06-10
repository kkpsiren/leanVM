use std::sync::OnceLock;

use field::PrimeCharacteristicRing;
use goldilocks::{Goldilocks, Poseidon1Goldilocks8, default_goldilocks_poseidon1_8};

use crate::{CAPACITY, DIGEST_ELEMS, RATE, WIDTH};

pub type Poseidon8 = Poseidon1Goldilocks8;

static POSEIDON_8_INSTANCE: OnceLock<Poseidon8> = OnceLock::new();
static POSEIDON_8_OF_ZERO: OnceLock<[Goldilocks; 4]> = OnceLock::new();

#[inline(always)]
pub fn get_poseidon8() -> &'static Poseidon8 {
    POSEIDON_8_INSTANCE.get_or_init(default_goldilocks_poseidon1_8)
}

#[inline(always)]
pub fn get_poseidon_8_of_zero() -> &'static [Goldilocks; 4] {
    POSEIDON_8_OF_ZERO.get_or_init(|| poseidon8_compress([Goldilocks::default(); 8]))
}

#[inline(always)]
pub fn poseidon8_compress(input: [Goldilocks; 8]) -> [Goldilocks; 4] {
    let mut state = input;
    get_poseidon8().compress_in_place(&mut state);
    state[0..4].try_into().unwrap()
}

#[inline(always)]
pub fn poseidon8_permute(input: [Goldilocks; 8]) -> [Goldilocks; 8] {
    get_poseidon8().permute(input)
}

pub fn poseidon8_compress_pair(left: &[Goldilocks; 4], right: &[Goldilocks; 4]) -> [Goldilocks; 4] {
    let mut input = [Goldilocks::default(); 8];
    input[..4].copy_from_slice(left);
    input[4..].copy_from_slice(right);
    poseidon8_compress(input)
}

// Overwrite-sponge
pub fn poseidon_hash_slice(data: &[Goldilocks]) -> [Goldilocks; DIGEST_ELEMS] {
    assert!(!data.is_empty());
    assert!(data.len().is_multiple_of(RATE));
    let mut state = [Goldilocks::default(); WIDTH];
    state[0] = Goldilocks::from_usize(data.len());
    for chunk in data.chunks(RATE) {
        state[CAPACITY..].copy_from_slice(chunk);
        state = poseidon8_permute(state);
    }
    state[CAPACITY..].try_into().unwrap()
}
