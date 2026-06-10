#![cfg_attr(not(test), warn(unused_crate_dependencies))]
use backend::PrimeCharacteristicRing;
use backend::{DIGEST_LEN_FE, Goldilocks, POSEIDON1_WIDTH, poseidon8_compress};

pub mod signers_cache;
mod wots;
pub use wots::*;
mod xmss;
pub use xmss::*;

pub const XMSS_DIGEST_LEN: usize = 2;
pub(crate) const TWEAK_LEN: usize = 1;

type F = Goldilocks;
type Digest = [F; XMSS_DIGEST_LEN];
type PublicParam = [F; PUBLIC_PARAM_LEN_FE];
type Randomness = [F; RANDOMNESS_LEN_FE];

// WOTS
pub const V: usize = 40;
pub const W: usize = 3;
pub const CHAIN_LENGTH: usize = 1 << W;
pub const NUM_CHAIN_HASHES: usize = 110;
pub const TARGET_SUM: usize = V * (CHAIN_LENGTH - 1) - NUM_CHAIN_HASHES;
pub const ENCODING_NUM_FINAL_ZEROS: usize = 8;
const _: () = assert!(V * W + ENCODING_NUM_FINAL_ZEROS == DIGEST_LEN_FE * 32);
const _: () = assert!(V.is_multiple_of(DIGEST_LEN_FE)); // V chunks split evenly across the 4 FEs
const _: () = assert!(ENCODING_NUM_FINAL_ZEROS.is_multiple_of(DIGEST_LEN_FE)); // same for the zero bits
pub const RANDOMNESS_LEN_FE: usize = 3;
pub const MESSAGE_LEN_FE: usize = 4;
pub const PUBLIC_PARAM_LEN_FE: usize = 2;
pub const PUB_KEY_FLAT_SIZE: usize = XMSS_DIGEST_LEN + PUBLIC_PARAM_LEN_FE;
pub const WOTS_SIG_SIZE_FE: usize = RANDOMNESS_LEN_FE + V * XMSS_DIGEST_LEN;

// XMSS
pub const LOG_LIFETIME: usize = 32;

// Tweak: domain separation within each hash.
pub const TWEAK_TYPE_CHAIN: usize = 0;
pub const TWEAK_TYPE_WOTS_PK: usize = 1;
pub const TWEAK_TYPE_MERKLE: usize = 2;
pub const TWEAK_TYPE_ENCODING: usize = 3;

const _: () = assert!(V.is_multiple_of(2)); // For efficiency of the snark (we can batch chains in pairs)

pub(crate) const PRF_DOMAINSEP_WOTS_SECRET_KEY: u32 = 1000;
pub(crate) const PRF_DOMAINSEP_PUBLIC_PARAM: u32 = 1001;
pub(crate) const PRF_DOMAINSEP_RANDOM_NODE: u32 = 1002;

/// Deterministic Poseidon PRF for key generation (replaces the former Keccak PRF).
///
/// Goldilocks holds 63 bits per element, so the 256-bit seed packs into 5 limbs (vs
/// 9 on a 31-bit field) and each index (< 2^60) fits in one element. The whole
/// `(domain, seed, indices)` tuple thus fits in a single width-8 compression.
pub(crate) fn poseidon_prf(domain: u32, seed: &[u8; 32], indices: [usize; 2]) -> [F; DIGEST_LEN_FE] {
    let mut input = [F::ZERO; POSEIDON1_WIDTH];
    input[0] = F::from_u32(domain);
    // Pack the 256-bit seed into 5 little-endian limbs of 63 bits: input[1..=5].
    let mut acc: u128 = 0;
    let mut acc_bits = 0u32;
    let mut limb = 1;
    for &byte in seed {
        acc |= u128::from(byte) << acc_bits;
        acc_bits += 8;
        if acc_bits >= 63 {
            input[limb] = F::from_u64((acc & ((1u128 << 63) - 1)) as u64);
            acc >>= 63;
            acc_bits -= 63;
            limb += 1;
        }
    }
    input[limb] = F::from_u64(acc as u64); // trailing 4 bits -> input[5]
    for (i, &idx) in indices.iter().enumerate() {
        assert!(idx < 1 << 60);
        input[6 + i] = F::from_usize(idx);
    }
    poseidon8_compress(input)
}

/// index = slot or node_index in Merkle tree
///
/// Goldilocks (64-bit field): the entire `(tweak_type, sub_position, index)` tuple
/// fits comfortably in one field element. We pack:
///   bits  0..32 : index (u32)
///   bits 32..42 : sub_position (10 bits)
///   bits 42..44 : tweak_type (2 bits)
pub fn make_tweak(tweak_type: usize, sub_position: usize, index: u32) -> [F; TWEAK_LEN] {
    assert!(tweak_type < 4);
    assert!(sub_position < 1 << 10);
    let packed = ((tweak_type as u64) << 42) | ((sub_position as u64) << 32) | u64::from(index);
    [F::from_u64(packed)]
}

/// `[tweak(1) | zeros(1) | public_param(2) | left_child(2) | right_child(2)]`
pub(crate) fn build_merkle_data(
    tweak: [F; TWEAK_LEN],
    public_param: &PublicParam,
    left_child: &Digest,
    right_child: &Digest,
) -> [F; POSEIDON1_WIDTH] {
    let mut data = [F::default(); POSEIDON1_WIDTH];
    data[..TWEAK_LEN].copy_from_slice(&tweak);
    // data[1..2] = zeros (default)
    data[DIGEST_LEN_FE - PUBLIC_PARAM_LEN_FE..][..PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
    data[DIGEST_LEN_FE..][..XMSS_DIGEST_LEN].copy_from_slice(left_child);
    data[DIGEST_LEN_FE + XMSS_DIGEST_LEN..].copy_from_slice(right_child);
    data
}

/// `[tweak(1) | zeros(1) | data(2)]`
pub(crate) fn build_left_chain_input(tweak: [F; TWEAK_LEN], data: &Digest) -> [F; DIGEST_LEN_FE] {
    let mut left = [F::default(); DIGEST_LEN_FE];
    left[..TWEAK_LEN].copy_from_slice(&tweak);
    left[DIGEST_LEN_FE - XMSS_DIGEST_LEN..].copy_from_slice(data);
    left
}

/// `[public_param(2) | zeros(2)]`
pub(crate) fn build_right_chain_input(public_param: &PublicParam) -> [F; DIGEST_LEN_FE] {
    let mut right = [F::default(); DIGEST_LEN_FE];
    right[..PUBLIC_PARAM_LEN_FE].copy_from_slice(public_param);
    right
}
