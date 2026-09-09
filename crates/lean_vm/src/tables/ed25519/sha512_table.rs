//! T2 `Sha512` as a VM table: `sha512(block_ptr, out_ptr, zero_ptr)`.
//!   reads  m[block_ptr .. +128] = one padded SHA-512 block (bytes, standard order)
//!   writes m[out_ptr .. +64]    = the 64-byte digest (standard byte order)
//!   zero_ptr must point at ≥ 64 zero cells (the lookup target of rows that carry no message/digest).
//! One block = 21 rows (20 round rows of 4 rounds + 1 digest row), the port of the M2 AIR
//! (`crates/ed_air/src/sha512.rs`, itself ported from OpenVM's sha2-air) plus the interconnect:
//! the row-0 flag is the execution-bus multiplicity, the three pointers are copied along the block,
//! rows 0..3 look up 32 message bytes each (bit-composed), the digest row looks up its 64 bytes.
//! Carries of the round additions are U4 range pushes; the digest bytes are U8 pushes.

use crate::execution::memory::MemoryAccess;
use crate::*;
use backend::*;

pub const SHA512_NAME: &str = "sha512";
pub const LOGUP_SHA512_DOMAINSEP: usize = 18;

pub const ROUNDS_PER_ROW: usize = 4;
pub const ROUND_ROWS: usize = 20;
pub const ROWS_PER_BLOCK: usize = 21;
pub const WORD_BITS: usize = 64;
pub const WORD_U16S: usize = 4;
pub const WORD_U8S: usize = 8;
pub const HASH_WORDS: usize = 8;

// interconnect columns
pub const COL_NU_A: usize = 0;
pub const COL_NU_B: usize = 1;
pub const COL_NU_C: usize = 2;
pub const COL_IDX_IN: usize = 3;
pub const COL_IDX_OUT: usize = 4;
pub const COL_IN: usize = 5;             // 32: message bytes of this row's 4 words (rows 0..3)
pub const COL_OUT: usize = 37;           // 64: digest bytes (digest row)
pub const BASE: usize = 101;
// the M2 layout, shifted by BASE
pub const COL_FLAGS: usize = BASE; // r[0..21]
pub const COL_W: usize = COL_FLAGS + ROWS_PER_BLOCK;
pub const COL_CARRY_W: usize = COL_W + ROUNDS_PER_ROW * WORD_BITS;
pub const COL_A: usize = COL_CARRY_W + ROUNDS_PER_ROW * WORD_U16S * 2;
pub const COL_E: usize = COL_A + ROUNDS_PER_ROW * WORD_BITS;
pub const COL_CARRY_A: usize = COL_E + ROUNDS_PER_ROW * WORD_BITS;
pub const COL_CARRY_E: usize = COL_CARRY_A + ROUNDS_PER_ROW * WORD_U16S;
pub const COL_W3: usize = COL_CARRY_E + ROUNDS_PER_ROW * WORD_U16S;
pub const COL_INTERMED_4: usize = COL_W3 + (ROUNDS_PER_ROW - 1) * WORD_U16S;
pub const COL_INTERMED_8: usize = COL_INTERMED_4 + ROUNDS_PER_ROW * WORD_U16S;
pub const COL_INTERMED_12: usize = COL_INTERMED_8 + ROUNDS_PER_ROW * WORD_U16S;
pub const N_COLS: usize = COL_INTERMED_12 + ROUNDS_PER_ROW * WORD_U16S; // 1,015
pub const COL_MULT: usize = COL_FLAGS; // row-0 flag

pub const SHA512_K: [u64; 80] = [
    0x428a2f98d728ae22, 0x7137449123ef65cd, 0xb5c0fbcfec4d3b2f, 0xe9b5dba58189dbbc, 0x3956c25bf348b538, 0x59f111f1b605d019, 0x923f82a4af194f9b, 0xab1c5ed5da6d8118,
    0xd807aa98a3030242, 0x12835b0145706fbe, 0x243185be4ee4b28c, 0x550c7dc3d5ffb4e2, 0x72be5d74f27b896f, 0x80deb1fe3b1696b1, 0x9bdc06a725c71235, 0xc19bf174cf692694,
    0xe49b69c19ef14ad2, 0xefbe4786384f25e3, 0x0fc19dc68b8cd5b5, 0x240ca1cc77ac9c65, 0x2de92c6f592b0275, 0x4a7484aa6ea6e483, 0x5cb0a9dcbd41fbd4, 0x76f988da831153b5,
    0x983e5152ee66dfab, 0xa831c66d2db43210, 0xb00327c898fb213f, 0xbf597fc7beef0ee4, 0xc6e00bf33da88fc2, 0xd5a79147930aa725, 0x06ca6351e003826f, 0x142929670a0e6e70,
    0x27b70a8546d22ffc, 0x2e1b21385c26c926, 0x4d2c6dfc5ac42aed, 0x53380d139d95b3df, 0x650a73548baf63de, 0x766a0abb3c77b2a8, 0x81c2c92e47edaee6, 0x92722c851482353b,
    0xa2bfe8a14cf10364, 0xa81a664bbc423001, 0xc24b8b70d0f89791, 0xc76c51a30654be30, 0xd192e819d6ef5218, 0xd69906245565a910, 0xf40e35855771202a, 0x106aa07032bbd1b8,
    0x19a4c116b8d2d0c8, 0x1e376c085141ab53, 0x2748774cdf8eeb99, 0x34b0bcb5e19b48a8, 0x391c0cb3c5c95a63, 0x4ed8aa4ae3418acb, 0x5b9cca4f7763e373, 0x682e6ff3d6b2b8a3,
    0x748f82ee5defb2fc, 0x78a5636f43172f60, 0x84c87814a1f0ab72, 0x8cc702081a6439ec, 0x90befffa23631e28, 0xa4506cebde82bde9, 0xbef9a3f7b2c67915, 0xc67178f2e372532b,
    0xca273eceea26619c, 0xd186b8c721c0c207, 0xeada7dd6cde0eb1e, 0xf57d4f7fee6ed178, 0x06f067aa72176fba, 0x0a637dc5a2c898a6, 0x113f9804bef90dae, 0x1b710b35131c471b,
    0x28db77f523047d84, 0x32caab7b40c72493, 0x3c9ebe0a15c9bebc, 0x431d67c49c100d4c, 0x4cc5d4becb3e42b6, 0x597f299cfc657e2a, 0x5fcb6fab3ad6faec, 0x6c44198c4a475817,
];
pub const SHA512_H: [u64; 8] = [
    0x6a09e667f3bcc908, 0xbb67ae8584caa73b, 0x3c6ef372fe94f82b, 0xa54ff53a5f1d36f1, 0x510e527fade682d1, 0x9b05688c2b3e6c1f, 0x1f83d9abfb41bd6b, 0x5be0cd19137e2179,
];

pub fn word_bits(x: u64) -> [u64; 64] { std::array::from_fn(|i| (x >> i) & 1) }
pub fn word_limbs(x: u64) -> [u64; 4] { std::array::from_fn(|i| (x >> (16 * i)) & 0xffff) }
fn big_sig0(x: u64) -> u64 { x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39) }
fn big_sig1(x: u64) -> u64 { x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41) }
fn small_sig0(x: u64) -> u64 { x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7) }
fn small_sig1(x: u64) -> u64 { x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6) }
fn ch(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (!x & z) }
fn maj(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (x & z) ^ (y & z) }

/// SHA-512 padding of a message that fits one block (≤ 111 bytes) → 128 bytes.
pub fn pad_single_block(msg: &[u8]) -> [u8; 128] {
    assert!(msg.len() <= 111, "single-block SHA-512 messages are at most 111 bytes");
    let mut block = [0u8; 128];
    block[..msg.len()].copy_from_slice(msg);
    block[msg.len()] = 0x80;
    block[112..].copy_from_slice(&((msg.len() as u128) * 8).to_be_bytes());
    block
}
pub fn block_words(block: &[u8; 128]) -> [u64; 16] { std::array::from_fn(|i| u64::from_be_bytes(block[8 * i..8 * i + 8].try_into().unwrap())) }
/// Native SHA-512 of one padded block from the IV.
pub fn sha512_block(words: &[u64; 16]) -> [u64; 8] {
    sha512_compress(words, &SHA512_H)
}
fn sha512_compress(words: &[u64; 16], initial: &[u64; 8]) -> [u64; 8] {
    let mut w = [0u64; 80];
    w[..16].copy_from_slice(words);
    for t in 16..80 { w[t] = small_sig1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(small_sig0(w[t - 15])).wrapping_add(w[t - 16]); }
    let mut s = *initial;
    for t in 0..80 {
        let t1 = s[7].wrapping_add(big_sig1(s[4])).wrapping_add(ch(s[4], s[5], s[6])).wrapping_add(SHA512_K[t]).wrapping_add(w[t]);
        let t2 = big_sig0(s[0]).wrapping_add(maj(s[0], s[1], s[2]));
        s = [t1.wrapping_add(t2), s[0], s[1], s[2], s[3].wrapping_add(t1), s[4], s[5], s[6]];
    }
    std::array::from_fn(|i| initial[i].wrapping_add(s[i]))
}

/// Standard SHA-512 for arbitrary byte strings, reusing the VM's compression implementation.
/// The input is borrowed; padding uses at most two stack blocks.
pub fn sha512_bytes(bytes: &[u8]) -> [u8; 64] {
    let mut state = SHA512_H;
    let mut chunks = bytes.chunks_exact(128);
    for block in &mut chunks {
        state = sha512_compress(&block_words(block.try_into().unwrap()), &state);
    }
    let tail = chunks.remainder();
    let mut padding = [0u8; 256];
    padding[..tail.len()].copy_from_slice(tail);
    padding[tail.len()] = 0x80;
    let padded_len = if tail.len() < 112 { 128 } else { 256 };
    padding[padded_len - 16..padded_len].copy_from_slice(&((bytes.len() as u128) * 8).to_be_bytes());
    for block in padding[..padded_len].chunks_exact(128) {
        state = sha512_compress(&block_words(block.try_into().unwrap()), &state);
    }
    digest_bytes(&state)
}
/// The digest in standard byte order (big-endian words).
pub fn digest_bytes(final_hash: &[u64; 8]) -> [u8; 64] { let mut d = [0u8; 64]; for i in 0..8 { d[8 * i..8 * i + 8].copy_from_slice(&final_hash[i].to_be_bytes()); } d }

// ---- symbolic helpers ----
fn rotr<T: Clone>(bits: &[T], n: usize) -> Vec<T> { (0..bits.len()).map(|i| bits[(i + n) % bits.len()].clone()).collect() }
fn shr<T: PrimeCharacteristicRing + Clone>(bits: &[T], n: usize) -> Vec<T> { (0..bits.len()).map(|i| if i + n < bits.len() { bits[i + n].clone() } else { T::ZERO }).collect() }
fn xor3<T: PrimeCharacteristicRing + Clone>(x: &[T], y: &[T], z: &[T]) -> Vec<T> {
    (0..x.len()).map(|i| {
        let (a, b, c) = (x[i].clone(), y[i].clone(), z[i].clone());
        let ab = a.clone() * b.clone(); let bc = b.clone() * c.clone(); let ca = c.clone() * a.clone();
        a + b + c - (ab.clone() + bc + ca).double() + (ab * c).double().double()
    }).collect()
}
fn big_sig0_f<T: PrimeCharacteristicRing + Clone>(x: &[T]) -> Vec<T> { xor3(&rotr(x, 28), &rotr(x, 34), &rotr(x, 39)) }
fn big_sig1_f<T: PrimeCharacteristicRing + Clone>(x: &[T]) -> Vec<T> { xor3(&rotr(x, 14), &rotr(x, 18), &rotr(x, 41)) }
fn small_sig0_f<T: PrimeCharacteristicRing + Clone>(x: &[T]) -> Vec<T> { xor3(&rotr(x, 1), &rotr(x, 8), &shr(x, 7)) }
fn small_sig1_f<T: PrimeCharacteristicRing + Clone>(x: &[T]) -> Vec<T> { xor3(&rotr(x, 19), &rotr(x, 61), &shr(x, 6)) }
fn ch_f<T: PrimeCharacteristicRing + Clone>(x: &[T], y: &[T], z: &[T]) -> Vec<T> { (0..x.len()).map(|i| x[i].clone() * (y[i].clone() - z[i].clone()) + z[i].clone()).collect() }
fn maj_f<T: PrimeCharacteristicRing + Clone>(x: &[T], y: &[T], z: &[T]) -> Vec<T> {
    (0..x.len()).map(|i| { let (a, b, c) = (x[i].clone(), y[i].clone(), z[i].clone()); a.clone() * b.clone() + a.clone() * c.clone() + b.clone() * c.clone() - (a * b * c).double() }).collect()
}
fn limb<T: PrimeCharacteristicRing + Clone, Fb: PrimeCharacteristicRing>(bits: &[T], j: usize, mul: impl Fn(T, Fb) -> T) -> T {
    let mut acc = T::ZERO; let mut pow = Fb::ONE;
    for b in &bits[16 * j..16 * j + 16] { acc += mul(b.clone(), pow.clone()); pow = pow.double(); }
    acc
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sha512Table<const BUS: bool>;

impl<const BUS: bool> Air for Sha512Table<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 5 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { N_COLS }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let cur: Vec<AB::IF> = builder.flat().to_vec();
        let nxt: Vec<AB::IF> = builder.shift().to_vec();
        let f = |x: u64| AB::F::from_usize(x as usize);
        let mulf = |t: AB::IF, c: AB::F| t * c;
        let bits = |row: &[AB::IF], base: usize, i: usize| -> Vec<AB::IF> { row[base + i * WORD_BITS..base + (i + 1) * WORD_BITS].to_vec() };
        let r = |row: &[AB::IF], k: usize| row[COL_FLAGS + k].clone();
        let sum_flags = |row: &[AB::IF], lo: usize, hi: usize| (lo..hi).fold(AB::IF::ZERO, |a, k| a + r(row, k));

        // execution bus: pulled once per block by the row-0 flag
        let mult = r(&cur, 0);
        let (nu_a, nu_b, nu_c) = (cur[COL_NU_A].clone(), cur[COL_NU_B].clone(), cur[COL_NU_C].clone());
        let ds = AB::IF::from_usize(LOGUP_SHA512_DOMAINSEP);
        if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, mult, ds, &[nu_a.clone(), nu_b.clone(), nu_c.clone()]); }
        else { builder.declare_values(&[mult]); builder.declare_values(&[nu_a.clone(), nu_b.clone(), nu_c.clone(), ds]); }

        let cur_pad = AB::IF::ONE - sum_flags(&cur, 0, ROWS_PER_BLOCK);
        let nxt_pad = AB::IF::ONE - sum_flags(&nxt, 0, ROWS_PER_BLOCK);
        let nxt_round_ge1 = sum_flags(&nxt, 1, ROUND_ROWS);
        let nxt_ge4 = sum_flags(&nxt, 4, ROUND_ROWS);
        let cur_round = sum_flags(&cur, 0, ROUND_ROWS);
        let is_msg = sum_flags(&cur, 0, 4);
        let is_digest = r(&cur, ROUND_ROWS);
        let rowidx = r(&cur, 1) + r(&cur, 2).double() + r(&cur, 3) * f(3);

        // interconnect: pointers copied along the block (next row is row 1..20); lookup indices; byte columns
        let in_block_next = nxt_round_ge1.clone() + r(&nxt, ROUND_ROWS);
        for c in [COL_NU_A, COL_NU_B, COL_NU_C] { builder.assert_zero(in_block_next.clone() * (nxt[c].clone() - cur[c].clone())); }
        builder.assert_zero(cur[COL_IDX_IN].clone() - (is_msg.clone() * nu_a + rowidx * f(32) + (AB::IF::ONE - is_msg.clone()) * nu_c.clone()));
        builder.assert_zero(cur[COL_IDX_OUT].clone() - (is_digest.clone() * nu_b + (AB::IF::ONE - is_digest.clone()) * nu_c));
        for i in 0..ROUNDS_PER_ROW { for k in 0..WORD_U8S {
            // standard byte k of word i = bits [8(7−k) .. 8(7−k)+8) (little-endian bits)
            let mut byte = AB::IF::ZERO;
            for t in 0..8 { byte += mulf(cur[COL_W + i * WORD_BITS + 8 * (7 - k) + t].clone(), f(1 << t)); }
            builder.assert_zero(cur[COL_IN + i * WORD_U8S + k].clone() - is_msg.clone() * byte);
        } }
        for j in 0..64 { builder.assert_zero(cur[COL_OUT + j].clone() - is_digest.clone() * cur[COL_W + j].clone()); }

        // 1. flags boolean, one-hot (padding = no flag), row transitions
        for k in 0..ROWS_PER_BLOCK { builder.assert_bool(r(&cur, k)); }
        builder.assert_bool(cur_pad.clone());
        for k in 0..ROUND_ROWS { builder.assert_zero(r(&nxt, k + 1) - r(&cur, k)); }
        builder.assert_zero(r(&nxt, 0) + nxt_pad.clone() - r(&cur, ROUND_ROWS) - cur_pad.clone());
        builder.assert_zero(cur_pad.clone() * (AB::IF::ONE - nxt_pad.clone()));

        // 2. bits are boolean: a, e on every row; w on round rows
        for i in 0..ROUNDS_PER_ROW { for j in 0..WORD_BITS { builder.assert_bool(cur[COL_A + i * WORD_BITS + j].clone()); builder.assert_bool(cur[COL_E + i * WORD_BITS + j].clone()); } }
        for i in 0..ROUNDS_PER_ROW { for j in 0..WORD_BITS { let w = cur[COL_W + i * WORD_BITS + j].clone(); builder.assert_zero(cur_round.clone() * w.bool_check()); } }

        // 3. message schedule
        let w8: Vec<Vec<AB::IF>> = (0..2 * ROUNDS_PER_ROW).map(|i| if i < 4 { bits(&cur, COL_W, i) } else { bits(&nxt, COL_W, i - 4) }).collect();
        for i in 0..ROUNDS_PER_ROW - 1 { for j in 0..WORD_U16S {
            let expect = nxt[COL_W3 + i * WORD_U16S + j].clone();
            builder.assert_zero(nxt_round_ge1.clone() * (limb(&w8[i + 1], j, mulf) - expect));
        } }
        for i in 0..ROUNDS_PER_ROW {
            let sig = small_sig0_f(&w8[i + 1]);
            for j in 0..WORD_U16S {
                let v = limb(&w8[i], j, mulf) + limb(&sig, j, mulf);
                builder.assert_zero(nxt_round_ge1.clone() * (nxt[COL_INTERMED_4 + i * WORD_U16S + j].clone() - v));
            }
        }
        let nxt_2_17 = sum_flags(&nxt, 2, ROUND_ROWS - 2);
        let nxt_3_18 = sum_flags(&nxt, 3, ROUND_ROWS - 1);
        for i in 0..ROUNDS_PER_ROW { for j in 0..WORD_U16S {
            builder.assert_zero(nxt_2_17.clone() * (nxt[COL_INTERMED_8 + i * WORD_U16S + j].clone() - cur[COL_INTERMED_4 + i * WORD_U16S + j].clone()));
            builder.assert_zero(nxt_3_18.clone() * (nxt[COL_INTERMED_12 + i * WORD_U16S + j].clone() - cur[COL_INTERMED_8 + i * WORD_U16S + j].clone()));
        } }
        for i in 0..ROUNDS_PER_ROW {
            let sig1 = small_sig1_f(&w8[i + 2]);
            let w7: Vec<AB::IF> = if i < 3 { (0..WORD_U16S).map(|j| cur[COL_W3 + i * WORD_U16S + j].clone()).collect() } else { (0..WORD_U16S).map(|j| limb(&w8[i - 3], j, mulf)).collect() };
            let carries: Vec<AB::IF> = (0..WORD_U16S).map(|j| nxt[COL_CARRY_W + i * 8 + 2 * j].clone() + nxt[COL_CARRY_W + i * 8 + 2 * j + 1].clone().double()).collect();
            for j in 0..WORD_U16S {
                let mut lhs = if j == 0 { AB::IF::ZERO } else { carries[j - 1].clone() };
                lhs += limb(&sig1, j, mulf) + w7[j].clone() + cur[COL_INTERMED_12 + i * WORD_U16S + j].clone();
                let rhs = limb(&w8[i + 4], j, mulf) + carries[j].clone() * f(1 << 16);
                builder.assert_zero(nxt_ge4.clone() * (lhs - rhs));
                builder.assert_zero(nxt_ge4.clone() * nxt[COL_CARRY_W + i * 8 + 2 * j].clone().bool_check());
                builder.assert_zero(nxt_ge4.clone() * nxt[COL_CARRY_W + i * 8 + 2 * j + 1].clone().bool_check());
            }
        }

        // 4. work variables
        let iv_a: Vec<Vec<AB::IF>> = (0..4).map(|i| word_bits(SHA512_H[3 - i]).iter().map(|&b| AB::IF::from_usize(b as usize)).collect()).collect();
        let iv_e: Vec<Vec<AB::IF>> = (0..4).map(|i| word_bits(SHA512_H[7 - i]).iter().map(|&b| AB::IF::from_usize(b as usize)).collect()).collect();
        let k_limb = |row: &[AB::IF], i: usize, j: usize| -> AB::IF { (0..ROUND_ROWS).fold(AB::IF::ZERO, |acc, k| acc + r(row, k) * f(word_limbs(SHA512_K[k * ROUNDS_PER_ROW + i])[j])) };
        let round_constraints = |builder: &mut AB, gate: AB::IF, prev_a: &[Vec<AB::IF>], prev_e: &[Vec<AB::IF>], row: &[AB::IF]| {
            let a8: Vec<Vec<AB::IF>> = prev_a.iter().cloned().chain((0..4).map(|i| bits(row, COL_A, i))).collect();
            let e8: Vec<Vec<AB::IF>> = prev_e.iter().cloned().chain((0..4).map(|i| bits(row, COL_E, i))).collect();
            for i in 0..ROUNDS_PER_ROW {
                let w_limbs: Vec<AB::IF> = (0..WORD_U16S).map(|j| limb(&bits(row, COL_W, i), j, mulf)).collect();
                let h = &e8[i]; let d = &a8[i];
                let sig1 = big_sig1_f(&e8[i + 3]); let chv = ch_f(&e8[i + 3], &e8[i + 2], &e8[i + 1]);
                let sig0 = big_sig0_f(&a8[i + 3]); let mj = maj_f(&a8[i + 3], &a8[i + 2], &a8[i + 1]);
                for j in 0..WORD_U16S {
                    let t1 = limb(h, j, mulf) + limb(&sig1, j, mulf) + limb(&chv, j, mulf) + k_limb(row, i, j) + w_limbs[j].clone();
                    let ca = row[COL_CARRY_A + i * WORD_U16S + j].clone(); let ce = row[COL_CARRY_E + i * WORD_U16S + j].clone();
                    let ca_prev = if j == 0 { AB::IF::ZERO } else { row[COL_CARRY_A + i * WORD_U16S + j - 1].clone() };
                    let ce_prev = if j == 0 { AB::IF::ZERO } else { row[COL_CARRY_E + i * WORD_U16S + j - 1].clone() };
                    let lhs_a = t1.clone() + limb(&sig0, j, mulf) + limb(&mj, j, mulf) + ca_prev;
                    let rhs_a = limb(&a8[i + 4], j, mulf) + ca * f(1 << 16);
                    builder.assert_zero(gate.clone() * (lhs_a - rhs_a));
                    let lhs_e = limb(d, j, mulf) + t1 + ce_prev;
                    let rhs_e = limb(&e8[i + 4], j, mulf) + ce * f(1 << 16);
                    builder.assert_zero(gate.clone() * (lhs_e - rhs_e));
                }
            }
        };
        let prev_a: Vec<Vec<AB::IF>> = (0..4).map(|i| bits(&cur, COL_A, i)).collect();
        let prev_e: Vec<Vec<AB::IF>> = (0..4).map(|i| bits(&cur, COL_E, i)).collect();
        round_constraints(builder, nxt_round_ge1.clone(), &prev_a, &prev_e, &nxt);
        round_constraints(builder, r(&cur, 0), &iv_a, &iv_e, &cur);

        // 5. digest row (next): final[i] = IV[i] + work_vars[i]; bytes in STANDARD order in next.w[0..64]:
        //    limb j (little-endian 16-bit) of word i = bytes 8i+7−2j (lo) and 8i+6−2j (hi)
        let is_digest_next = r(&nxt, ROUND_ROWS);
        let inv16 = AB::F::from_usize(F::from_usize(1 << 16).inverse().as_canonical_u32() as usize);
        for i in 0..HASH_WORDS {
            let wv: Vec<AB::IF> = if i < 4 { bits(&cur, COL_A, 3 - i) } else { bits(&cur, COL_E, 7 - i) };
            let mut carry = AB::IF::ZERO;
            for j in 0..WORD_U16S {
                let lo = nxt[COL_W + i * WORD_U8S + 7 - 2 * j].clone(); let hi = nxt[COL_W + i * WORD_U8S + 6 - 2 * j].clone();
                let final_limb = lo + hi * f(256);
                let sum = carry + limb(&wv, j, mulf) + f(word_limbs(SHA512_H[i])[j]) - final_limb;
                carry = sum * inv16.clone();
                builder.assert_zero(is_digest_next.clone() * carry.clone().bool_check());
            }
        }
    }
}
// bus 2 + interconnect (3 + 1 + 1 + 32 + 64) + the M2 constraints
pub const N_CONSTRAINTS: usize = 2 + 101 + (22 + 20 + 2 + 512 + 256 + 12 + 16 + 32 + 48 + 64 + 32);

impl<const BUS: bool> TableT for Sha512Table<BUS> {
    fn name(&self) -> &'static str { "sha512" }
    fn table(&self) -> Table { Table::sha512() }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(COL_MULT),
            domainsep: BusData::Constant(LOGUP_SHA512_DOMAINSEP),
            data: vec![BusData::Column(COL_NU_A), BusData::Column(COL_NU_B), BusData::Column(COL_NU_C)],
        }];
        buses.extend(memory_lookups_consecutive(COL_IDX_IN, COL_IN, 32));
        buses.extend(memory_lookups_consecutive(COL_IDX_OUT, COL_OUT, 64));
        for (section, cols) in range_cols() { buses.extend(range_lookups(&cols, section)); }
        buses
    }
    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; N_COLS];
        for c in [COL_NU_A, COL_NU_B, COL_NU_C, COL_IDX_IN, COL_IDX_OUT] { row[c] = F::from_usize(zero_vec_ptr); }
        row
    }
    #[inline(always)]
    fn execute<M: MemoryAccess>(&self, arg_a: F, arg_b: F, arg_c: F, _args: PrecompileCompTimeArgs<usize>, ctx: &mut InstructionContext<'_, M>) -> Result<(), RunnerError> {
        let (in_ptr, out_ptr, zero_ptr) = (arg_a.to_usize(), arg_b.to_usize(), arg_c.to_usize());
        let mut cells = [F::ZERO; 128];
        ctx.memory.get_slice_into(in_ptr, &mut cells)?;
        let block: [u8; 128] = std::array::from_fn(|i| { let v = cells[i].as_canonical_u32(); assert!(v < 256, "sha512: block cell is not a byte"); v as u8 });
        let rows = block_rows(&block_words(&block), in_ptr, out_ptr, zero_ptr);
        ctx.memory.set_slice(out_ptr, &rows[ROUND_ROWS][COL_OUT..COL_OUT + 64])?;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        for row in &rows { for (i, v) in row.iter().enumerate() { trace.columns[i].push(*v); } }
        Ok(())
    }
}

/// Range classes: round carries (≤ 7) are U4, digest bytes U8. Everything else is boolean or a
/// linear function of booleans.
pub fn range_cols() -> Vec<(usize, Vec<usize>)> {
    vec![
        (RANGE_U4, (COL_CARRY_A..COL_CARRY_A + 2 * ROUNDS_PER_ROW * WORD_U16S).collect()),
        (RANGE_U8, (COL_OUT..COL_OUT + 64).collect()),
    ]
}

/// One block's 21 rows for padded `words`, with the interconnect columns for (in_ptr, out_ptr, zero_ptr).
pub fn block_rows(words: &[u64; 16], in_ptr: usize, out_ptr: usize, zero_ptr: usize) -> Vec<[F; N_COLS]> {
    let mut rows = vec![[F::ZERO; N_COLS]; ROWS_PER_BLOCK];
    let fu = |x: u64| F::from_usize(x as usize);
    let mut w = [0u64; 80];
    w[..16].copy_from_slice(words);
    for t in 16..80 { w[t] = small_sig1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(small_sig0(w[t - 15])).wrapping_add(w[t - 16]); }
    let mut s = SHA512_H;
    for rrow in 0..ROUND_ROWS {
        let row = &mut rows[rrow];
        row[COL_FLAGS + rrow] = F::ONE;
        for i in 0..ROUNDS_PER_ROW {
            let t = rrow * ROUNDS_PER_ROW + i;
            for (j, b) in word_bits(w[t]).iter().enumerate() { row[COL_W + i * WORD_BITS + j] = fu(*b); }
            if rrow >= 4 {
                let terms = [small_sig1(w[t - 2]), w[t - 7], small_sig0(w[t - 15]), w[t - 16]];
                let mut carry_in = 0u64;
                for j in 0..WORD_U16S {
                    let sum: u64 = terms.iter().map(|x| word_limbs(*x)[j]).sum::<u64>() + carry_in;
                    let carry = (sum - word_limbs(w[t])[j]) >> 16;
                    row[COL_CARRY_W + i * 8 + 2 * j] = fu(carry & 1); row[COL_CARRY_W + i * 8 + 2 * j + 1] = fu(carry >> 1);
                    carry_in = carry;
                }
            }
            let t1_terms = [s[7], big_sig1(s[4]), ch(s[4], s[5], s[6]), SHA512_K[t], w[t]];
            let t2_terms = [big_sig0(s[0]), maj(s[0], s[1], s[2])];
            let t1 = t1_terms.iter().fold(0u64, |a, x| a.wrapping_add(*x));
            let t2 = t2_terms.iter().fold(0u64, |a, x| a.wrapping_add(*x));
            let a = t1.wrapping_add(t2); let e = s[3].wrapping_add(t1);
            for (j, b) in word_bits(a).iter().enumerate() { row[COL_A + i * WORD_BITS + j] = fu(*b); }
            for (j, b) in word_bits(e).iter().enumerate() { row[COL_E + i * WORD_BITS + j] = fu(*b); }
            let (mut ca_in, mut ce_in) = (0u64, 0u64);
            for j in 0..WORD_U16S {
                let t1l: u64 = t1_terms.iter().map(|x| word_limbs(*x)[j]).sum();
                let t2l: u64 = t2_terms.iter().map(|x| word_limbs(*x)[j]).sum();
                let al = t1l + t2l + ca_in; let el = t1l + word_limbs(s[3])[j] + ce_in;
                let ca = (al - word_limbs(a)[j]) >> 16; let ce = (el - word_limbs(e)[j]) >> 16;
                row[COL_CARRY_A + i * WORD_U16S + j] = fu(ca); row[COL_CARRY_E + i * WORD_U16S + j] = fu(ce);
                ca_in = ca; ce_in = ce;
            }
            s = [a, s[0], s[1], s[2], e, s[4], s[5], s[6]];
        }
        if rrow >= 1 {
            for i in 0..ROUNDS_PER_ROW {
                let t = rrow * ROUNDS_PER_ROW + i;
                if i < 3 { for (j, l) in word_limbs(w[t - 3]).iter().enumerate() { row[COL_W3 + i * WORD_U16S + j] = fu(*l); } }
                let v4 = word_limbs(w[t - 4]); let sg = word_limbs(small_sig0(w[t - 3]));
                for j in 0..WORD_U16S { row[COL_INTERMED_4 + i * WORD_U16S + j] = fu(v4[j] + sg[j]); }
            }
        }
    }
    for rrow in 2..ROUND_ROWS - 2 { for c in 0..ROUNDS_PER_ROW * WORD_U16S { rows[rrow][COL_INTERMED_8 + c] = rows[rrow - 1][COL_INTERMED_4 + c]; } }
    for rrow in 3..ROUND_ROWS - 1 { for c in 0..ROUNDS_PER_ROW * WORD_U16S { rows[rrow][COL_INTERMED_12 + c] = rows[rrow - 1][COL_INTERMED_8 + c]; } }
    let digest = digest_bytes(&sha512_block(words));
    {
        let drow = &mut rows[ROUND_ROWS];
        drow[COL_FLAGS + ROUND_ROWS] = F::ONE;
        for (j, b) in digest.iter().enumerate() { drow[COL_W + j] = fu(*b as u64); drow[COL_OUT + j] = fu(*b as u64); }
    }
    // interconnect columns
    let block_bytes: Vec<u8> = words.iter().flat_map(|x| x.to_be_bytes()).collect();
    for (rrow, row) in rows.iter_mut().enumerate() {
        row[COL_NU_A] = F::from_usize(in_ptr); row[COL_NU_B] = F::from_usize(out_ptr); row[COL_NU_C] = F::from_usize(zero_ptr);
        if rrow < 4 {
            row[COL_IDX_IN] = F::from_usize(in_ptr + 32 * rrow);
            for k in 0..32 { row[COL_IN + k] = fu(block_bytes[32 * rrow + k] as u64); }
        } else { row[COL_IDX_IN] = F::from_usize(zero_ptr); }
        row[COL_IDX_OUT] = F::from_usize(if rrow == ROUND_ROWS { out_ptr } else { zero_ptr });
    }
    rows
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn native_sha512_matches_known_vector() {
        // SHA-512("abc")
        let d = digest_bytes(&sha512_block(&block_words(&pad_single_block(b"abc"))));
        let hex: String = d.iter().map(|b| format!("{b:02x}")).collect();
        assert_eq!(hex, "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f", "digest = {hex}");
    }
}
