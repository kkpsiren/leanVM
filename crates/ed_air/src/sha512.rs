//! SHA-512 single-block AIR for leanVM (M2 of docs/zk-aggregate-spec.md), ported from OpenVM's
//! `sha2-air` (Sha512Config: 4 rounds per row, 20 round rows + 1 digest row per block) to leanVM's
//! `flat()/shift()` builder.
//!
//! Differences from OpenVM, all deliberate:
//! - **No chaining.** Every block is a standalone message (`R ‖ A ‖ digest ‖ pad` is one block), so
//!   the state before round 0 is the IV constant and the digest row adds the IV: no `prev_hash`
//!   columns, no private bus.
//! - **Row 0 is anchored locally.** leanVM has no first-row selector and the last row's `shift` is
//!   itself, so the 4 rounds of a row-0 row are constrained from the IV and the row's OWN `w` (the
//!   "local form"); rows 1..19 use the (previous, current) pair form. A trace whose first row is not
//!   a row-0 row is therefore not a valid block start; the signature buses (M3) additionally require
//!   rows 0..2 to pull the message and the digest row to push the hash.
//! - **Flag-gated transitions instead of dummy fills.** OpenVM keeps degree ≤ 3 by asserting the
//!   round/schedule additions unconditionally and filling dummy carries/intermeds on rows where they
//!   do not apply. leanVM's sumcheck tolerates higher degree, so every transition is gated by the
//!   constrained row's one-hot flags and the trace holds only real values.
//! - **One-hot row flags** `r[0..21]` (round rows 0..19, digest row 20) replace the 6-cell
//!   polynomial encoder; `is_round`, `is_first_4`, `is_digest`, `is_padding` are linear in them.
//! - **The digest row aliases its 64 final-hash BYTES into the first 64 `w` cells** (unused there),
//!   so the row is not wider than a round row.
//!
//! Word convention: bits little-endian (bit 0 = LSB), 16-bit limbs little-endian, as in OpenVM.
//! Range checks (bytes on the digest row, carries ≤ 2^8 on round rows) are LogUp fractions and are
//! attached in M3; this AIR carries the boolean/arithmetic constraints only.

use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};

pub const ROUNDS_PER_ROW: usize = 4;
pub const ROUND_ROWS: usize = 20;
pub const ROWS_PER_BLOCK: usize = 21;
pub const WORD_BITS: usize = 64;
pub const WORD_U16S: usize = 4;
pub const WORD_U8S: usize = 8;
pub const HASH_WORDS: usize = 8;

// ---- column layout (every column is a shift column: the pair form reads the whole next row) ----
pub const COL_FLAGS: usize = 0; // r[0..21]
pub const COL_W: usize = COL_FLAGS + ROWS_PER_BLOCK; // 4 words × 64 bits (digest row: 64 bytes of final hash in the first 64 cells)
pub const COL_CARRY_W: usize = COL_W + ROUNDS_PER_ROW * WORD_BITS; // schedule carries: 4 words × 4 limbs × 2 bits
pub const COL_A: usize = COL_CARRY_W + ROUNDS_PER_ROW * WORD_U16S * 2; // 4 × 64 bits
pub const COL_E: usize = COL_A + ROUNDS_PER_ROW * WORD_BITS;
pub const COL_CARRY_A: usize = COL_E + ROUNDS_PER_ROW * WORD_BITS; // 4 × 4
pub const COL_CARRY_E: usize = COL_CARRY_A + ROUNDS_PER_ROW * WORD_U16S;
pub const COL_W3: usize = COL_CARRY_E + ROUNDS_PER_ROW * WORD_U16S; // 3 × 4 limbs
pub const COL_INTERMED_4: usize = COL_W3 + (ROUNDS_PER_ROW - 1) * WORD_U16S; // 4 × 4
pub const COL_INTERMED_8: usize = COL_INTERMED_4 + ROUNDS_PER_ROW * WORD_U16S;
pub const COL_INTERMED_12: usize = COL_INTERMED_8 + ROUNDS_PER_ROW * WORD_U16S;
pub const N_COLS: usize = COL_INTERMED_12 + ROUNDS_PER_ROW * WORD_U16S; // 914

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

// ---- native helpers ------------------------------------------------------------------------
pub fn word_bits(x: u64) -> [u64; 64] { std::array::from_fn(|i| (x >> i) & 1) }
pub fn word_limbs(x: u64) -> [u64; 4] { std::array::from_fn(|i| (x >> (16 * i)) & 0xffff) }
pub fn word_bytes(x: u64) -> [u64; 8] { std::array::from_fn(|i| (x >> (8 * i)) & 0xff) }
fn big_sig0(x: u64) -> u64 { x.rotate_right(28) ^ x.rotate_right(34) ^ x.rotate_right(39) }
fn big_sig1(x: u64) -> u64 { x.rotate_right(14) ^ x.rotate_right(18) ^ x.rotate_right(41) }
fn small_sig0(x: u64) -> u64 { x.rotate_right(1) ^ x.rotate_right(8) ^ (x >> 7) }
fn small_sig1(x: u64) -> u64 { x.rotate_right(19) ^ x.rotate_right(61) ^ (x >> 6) }
fn ch(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (!x & z) }
fn maj(x: u64, y: u64, z: u64) -> u64 { (x & y) ^ (x & z) ^ (y & z) }

/// SHA-512 padding of a message that fits one block (≤ 111 bytes): message ‖ 0x80 ‖ zeros ‖ len(128 bits, BE).
pub fn pad_single_block(msg: &[u8]) -> [u64; 16] {
    assert!(msg.len() <= 111, "single-block SHA-512 messages are at most 111 bytes");
    let mut block = [0u8; 128];
    block[..msg.len()].copy_from_slice(msg);
    block[msg.len()] = 0x80;
    let bits = (msg.len() as u128) * 8;
    block[112..].copy_from_slice(&bits.to_be_bytes());
    std::array::from_fn(|i| u64::from_be_bytes(block[8 * i..8 * i + 8].try_into().unwrap()))
}

/// Native SHA-512 of one padded block from the IV (the reference the AIR must reproduce).
pub fn sha512_block(words: &[u64; 16]) -> [u64; 8] {
    let mut w = [0u64; 80];
    w[..16].copy_from_slice(words);
    for t in 16..80 { w[t] = small_sig1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(small_sig0(w[t - 15])).wrapping_add(w[t - 16]); }
    let mut s = SHA512_H;
    for t in 0..80 {
        let t1 = s[7].wrapping_add(big_sig1(s[4])).wrapping_add(ch(s[4], s[5], s[6])).wrapping_add(SHA512_K[t]).wrapping_add(w[t]);
        let t2 = big_sig0(s[0]).wrapping_add(maj(s[0], s[1], s[2]));
        s = [t1.wrapping_add(t2), s[0], s[1], s[2], s[3].wrapping_add(t1), s[4], s[5], s[6]];
    }
    std::array::from_fn(|i| SHA512_H[i].wrapping_add(s[i]))
}

// ---- symbolic helpers (over the builder's IF) ------------------------------------------------
fn rotr<T: Clone>(bits: &[T], n: usize) -> Vec<T> { (0..bits.len()).map(|i| bits[(i + n) % bits.len()].clone()).collect() }
fn shr<T: PrimeCharacteristicRing + Clone>(bits: &[T], n: usize) -> Vec<T> { (0..bits.len()).map(|i| if i + n < bits.len() { bits[i + n].clone() } else { T::ZERO }).collect() }
fn xor3<T: PrimeCharacteristicRing + Clone>(x: &[T], y: &[T], z: &[T]) -> Vec<T> {
    // x ^ y ^ z for booleans: x + y + z − 2(xy + yz + zx) + 4xyz
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
/// Compose 16 little-endian bits into a limb value.
fn limb<T: PrimeCharacteristicRing + Clone, Fb: PrimeCharacteristicRing>(bits: &[T], j: usize, mul: impl Fn(T, Fb) -> T) -> T {
    let mut acc = T::ZERO; let mut pow = Fb::ONE;
    for b in &bits[16 * j..16 * j + 16] { acc += mul(b.clone(), pow.clone()); pow = pow.double(); }
    acc
}

#[derive(Debug, Clone, Copy, Default)]
pub struct Sha512Air;

impl Air for Sha512Air {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 5 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { N_COLS }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra: &Self::ExtraData) {
        let cur: Vec<AB::IF> = builder.flat().to_vec();
        let nxt: Vec<AB::IF> = builder.shift().to_vec();
        let f = |x: u64| AB::F::from_usize(x as usize);
        let mulf = |t: AB::IF, c: AB::F| t * c;
        let bits = |row: &[AB::IF], base: usize, i: usize| -> Vec<AB::IF> { row[base + i * WORD_BITS..base + (i + 1) * WORD_BITS].to_vec() };

        // flags (current / next)
        let r = |row: &[AB::IF], k: usize| row[COL_FLAGS + k].clone();
        let sum_flags = |row: &[AB::IF], lo: usize, hi: usize| (lo..hi).fold(AB::IF::ZERO, |a, k| a + r(row, k));
        let cur_pad = AB::IF::ONE - sum_flags(&cur, 0, ROWS_PER_BLOCK);
        let nxt_pad = AB::IF::ONE - sum_flags(&nxt, 0, ROWS_PER_BLOCK);
        let nxt_round = sum_flags(&nxt, 0, ROUND_ROWS);
        let nxt_round_ge1 = sum_flags(&nxt, 1, ROUND_ROWS);
        let nxt_ge4 = sum_flags(&nxt, 4, ROUND_ROWS);
        let cur_round = sum_flags(&cur, 0, ROUND_ROWS);

        // 1. flags boolean, one-hot (padding = no flag), row transitions
        for k in 0..ROWS_PER_BLOCK { builder.assert_bool(r(&cur, k)); }
        builder.assert_bool(cur_pad.clone());
        for k in 0..ROUND_ROWS { builder.assert_zero(r(&nxt, k + 1) - r(&cur, k)); }                 // round k -> row k+1 (round or digest)
        builder.assert_zero(r(&nxt, 0) + nxt_pad.clone() - r(&cur, ROUND_ROWS) - cur_pad.clone());   // digest/padding -> row 0 or padding
        builder.assert_zero(cur_pad.clone() * (AB::IF::ONE - nxt_pad.clone()));                       // padding -> padding

        // 2. bits are boolean: a, e on every row; w on round rows
        for i in 0..ROUNDS_PER_ROW { for j in 0..WORD_BITS { builder.assert_bool(cur[COL_A + i * WORD_BITS + j].clone()); builder.assert_bool(cur[COL_E + i * WORD_BITS + j].clone()); } }
        for i in 0..ROUNDS_PER_ROW { for j in 0..WORD_BITS { let w = cur[COL_W + i * WORD_BITS + j].clone(); builder.assert_zero(cur_round.clone() * w.bool_check()); } }

        // 3. message schedule (constrains the NEXT row's w for rows 4..19, and its helpers)
        let w8: Vec<Vec<AB::IF>> = (0..2 * ROUNDS_PER_ROW).map(|i| if i < 4 { bits(&cur, COL_W, i) } else { bits(&nxt, COL_W, i - 4) }).collect();
        // w_3 / intermed_4 of next row i = w[i+1] / w[i] + sig0(w[i+1]) for next rows 1..19 (row 0's helpers are never consumed)
        for i in 0..ROUNDS_PER_ROW - 1 { for j in 0..WORD_U16S {
            let expect = nxt[COL_W3 + i * WORD_U16S + j].clone();
            builder.assert_zero(nxt_round_ge1.clone() * (limb(&w8[i + 1], j, mulf) - expect));
        } }
        // intermed_4 of next = w[i] + sig0(w[i+1]) (limbs), when next is a round row
        for i in 0..ROUNDS_PER_ROW {
            let sig = small_sig0_f(&w8[i + 1]);
            for j in 0..WORD_U16S {
                let v = limb(&w8[i], j, mulf) + limb(&sig, j, mulf);
                builder.assert_zero(nxt_round_ge1.clone() * (nxt[COL_INTERMED_4 + i * WORD_U16S + j].clone() - v));
            }
        }
        // intermed_8 (next rows 2..17) = intermed_4 (cur); intermed_12 (next rows 3..18) = intermed_8 (cur)
        let nxt_2_17 = sum_flags(&nxt, 2, ROUND_ROWS - 2);
        let nxt_3_18 = sum_flags(&nxt, 3, ROUND_ROWS - 1);
        for i in 0..ROUNDS_PER_ROW { for j in 0..WORD_U16S {
            builder.assert_zero(nxt_2_17.clone() * (nxt[COL_INTERMED_8 + i * WORD_U16S + j].clone() - cur[COL_INTERMED_4 + i * WORD_U16S + j].clone()));
            builder.assert_zero(nxt_3_18.clone() * (nxt[COL_INTERMED_12 + i * WORD_U16S + j].clone() - cur[COL_INTERMED_8 + i * WORD_U16S + j].clone()));
        } }
        // schedule addition for next rows 4..19: w_t = sig1(w_{t-2}) + w_{t-7} + intermed_16 (= sig0(w_{t-15}) + w_{t-16})
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

        // 4. work variables: next.a/e[i] from the previous 4 rounds (pair form, next rows 1..19) or from the IV (local form, row 0)
        let iv_a: Vec<Vec<AB::IF>> = (0..4).map(|i| word_bits(SHA512_H[3 - i]).iter().map(|&b| AB::IF::from_usize(b as usize)).collect()).collect(); // a-side: h3,h2,h1,h0 in "rounds ago" order
        let iv_e: Vec<Vec<AB::IF>> = (0..4).map(|i| word_bits(SHA512_H[7 - i]).iter().map(|&b| AB::IF::from_usize(b as usize)).collect()).collect();
        let k_limb = |row: &[AB::IF], i: usize, j: usize| -> AB::IF { (0..ROUND_ROWS).fold(AB::IF::ZERO, |acc, k| acc + r(row, k) * f(word_limbs(SHA512_K[k * ROUNDS_PER_ROW + i])[j])) };
        let round_constraints = |builder: &mut AB, gate: AB::IF, prev_a: &[Vec<AB::IF>], prev_e: &[Vec<AB::IF>], row: &[AB::IF]| {
            // prev_*[i] = value i rounds ago (i = 0: one round ago ... wait: OpenVM order: local rows 0..3 then next rows; a[i+3] is 1 round before a[i+4])
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
                    // a = t1 + sig0(a) + maj(a,b,c)
                    let lhs_a = t1.clone() + limb(&sig0, j, mulf) + limb(&mj, j, mulf) + ca_prev;
                    let rhs_a = limb(&a8[i + 4], j, mulf) + ca * f(1 << 16);
                    builder.assert_zero(gate.clone() * (lhs_a - rhs_a));
                    // e = d + t1
                    let lhs_e = limb(d, j, mulf) + t1 + ce_prev;
                    let rhs_e = limb(&e8[i + 4], j, mulf) + ce * f(1 << 16);
                    builder.assert_zero(gate.clone() * (lhs_e - rhs_e));
                }
            }
        };
        let prev_a: Vec<Vec<AB::IF>> = (0..4).map(|i| bits(&cur, COL_A, i)).collect();
        let prev_e: Vec<Vec<AB::IF>> = (0..4).map(|i| bits(&cur, COL_E, i)).collect();
        round_constraints(builder, nxt_round_ge1.clone(), &prev_a, &prev_e, &nxt); // pair form
        round_constraints(builder, r(&cur, 0), &iv_a, &iv_e, &cur);                // local form (row 0)

        // 5. digest row (next): final[i] = IV[i] + work_vars[i] with boolean carries; bytes aliased in next.w[0..64]
        let is_digest = r(&nxt, ROUND_ROWS);
        let inv16 = AB::F::from_usize(F::from_usize(1 << 16).inverse().as_canonical_u32() as usize);
        for i in 0..HASH_WORDS {
            let wv: Vec<AB::IF> = if i < 4 { bits(&cur, COL_A, 3 - i) } else { bits(&cur, COL_E, 7 - i) };
            let mut carry = AB::IF::ZERO;
            for j in 0..WORD_U16S {
                let lo = nxt[COL_W + i * WORD_U8S + 2 * j].clone(); let hi = nxt[COL_W + i * WORD_U8S + 2 * j + 1].clone();
                let final_limb = lo + hi * f(256);
                let sum = carry + limb(&wv, j, mulf) + f(word_limbs(SHA512_H[i])[j]) - final_limb; // = carry_out · 2^16
                carry = sum * inv16.clone();
                builder.assert_zero(is_digest.clone() * carry.clone().bool_check());
            }
        }
    }
}

// constraint count: flags 22+20+2 + a/e 512 + w 256 + w3 12 + intermed4 16 + intermed8/12 32 + schedule 4*4*3 = 48 + rounds 2 forms × 4×4×2 = 64 + digest 32
pub const N_CONSTRAINTS: usize = 22 + 20 + 2 + 512 + 256 + 12 + 16 + 32 + 48 + 64 + 32;

// ---- trace generation --------------------------------------------------------------------------
/// One block's 21 rows (row-major, N_COLS each) for a padded message.
pub fn block_rows(words: &[u64; 16]) -> Vec<[F; N_COLS]> {
    let mut rows = vec![[F::ZERO; N_COLS]; ROWS_PER_BLOCK];
    let fu = |x: u64| F::from_usize(x as usize);
    let mut w = [0u64; 80];
    w[..16].copy_from_slice(words);
    for t in 16..80 { w[t] = small_sig1(w[t - 2]).wrapping_add(w[t - 7]).wrapping_add(small_sig0(w[t - 15])).wrapping_add(w[t - 16]); }
    // schedule carries (rows 4..19): per limb, the carry out of sig1(w_{t-2}) + w_{t-7} + sig0(w_{t-15}) + w_{t-16} (+carry in) - w_t
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
            // round
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
        // helpers, defined relative to the words visible from this row (t = rrow*4 + i): w_3 = w[t-3] (i<3), intermed_4 = w[t-4] + sig0(w[t-3])
        if rrow >= 1 {
            for i in 0..ROUNDS_PER_ROW {
                let t = rrow * ROUNDS_PER_ROW + i;
                if i < 3 { for (j, l) in word_limbs(w[t - 3]).iter().enumerate() { row[COL_W3 + i * WORD_U16S + j] = fu(*l); } }
                let v4 = word_limbs(w[t - 4]); let sg = word_limbs(small_sig0(w[t - 3]));
                for j in 0..WORD_U16S { row[COL_INTERMED_4 + i * WORD_U16S + j] = fu(v4[j] + sg[j]); }
            }
        }
    }
    // intermed_8 (rows 2..17) = intermed_4 of previous row; intermed_12 (rows 3..18) = intermed_8 of previous row
    for rrow in 2..ROUND_ROWS - 2 { for c in 0..ROUNDS_PER_ROW * WORD_U16S { rows[rrow][COL_INTERMED_8 + c] = rows[rrow - 1][COL_INTERMED_4 + c]; } }
    for rrow in 3..ROUND_ROWS - 1 { for c in 0..ROUNDS_PER_ROW * WORD_U16S { rows[rrow][COL_INTERMED_12 + c] = rows[rrow - 1][COL_INTERMED_8 + c]; } }
    // digest row
    let digest = &mut rows[ROUND_ROWS];
    digest[COL_FLAGS + ROUND_ROWS] = F::ONE;
    let final_hash = sha512_block(words);
    for i in 0..HASH_WORDS { for (j, b) in word_bytes(final_hash[i]).iter().enumerate() { digest[COL_W + i * WORD_U8S + j] = fu(*b); } }
    rows
}

/// Column-major trace for `messages` (each ≤ 111 bytes, one block), padded with zero rows to `n_rows`.
pub fn generate_trace(messages: &[Vec<u8>], n_rows: usize) -> Vec<Vec<F>> {
    assert!(messages.len() * ROWS_PER_BLOCK < n_rows, "need at least one padding row");
    let mut cols: Vec<Vec<F>> = (0..N_COLS).map(|_| vec![F::ZERO; n_rows]).collect();
    let mut r = 0;
    for m in messages {
        for row in block_rows(&pad_single_block(m)) { for c in 0..N_COLS { cols[c][r] = row[c]; } r += 1; }
    }
    cols
}

/// Debug builder: evaluates every constraint natively on (row, next row) and reports the first failure.
pub struct DebugBuilder<'a> { pub flat: &'a [F], pub shift: &'a [F], pub idx: usize, pub failures: Vec<usize> }
impl<'a> AirBuilder for DebugBuilder<'a> {
    type F = F; type IF = F; type EF = EF;
    fn flat(&self) -> &[F] { self.flat }
    fn shift(&self) -> &[F] { self.shift }
    fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.failures.push(self.idx); } self.idx += 1; }
    fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.failures.push(self.idx); } self.idx += 1; }
}
/// Returns (row, constraint index) of the first violated constraint, or None.
pub fn check_trace(cols: &[Vec<F>]) -> Option<(usize, usize)> {
    let n_rows = cols[0].len();
    let extra = ExtraDataForBuses::new(&[], vec![]);
    for r in 0..n_rows {
        let flat: Vec<F> = (0..N_COLS).map(|c| cols[c][r]).collect();
        let shift: Vec<F> = (0..N_COLS).map(|c| cols[c][(r + 1).min(n_rows - 1)]).collect();
        let mut b = DebugBuilder { flat: &flat, shift: &shift, idx: 0, failures: vec![] };
        Sha512Air.eval(&mut b, &extra);
        assert_eq!(b.idx, N_CONSTRAINTS, "N_CONSTRAINTS mismatch: counted {}", b.idx);
        if let Some(&c) = b.failures.first() { return Some((r, c)); }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn native_sha512_matches_fips_vectors() {
        let hx = |h: [u64; 8]| h.iter().map(|w| format!("{w:016x}")).collect::<String>();
        assert_eq!(hx(sha512_block(&pad_single_block(b"abc"))), "ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f");
        assert_eq!(hx(sha512_block(&pad_single_block(b""))), "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e");
    }

    #[test]
    fn honest_trace_satisfies_every_constraint() {
        let msgs: Vec<Vec<u8>> = vec![b"abc".to_vec(), vec![], (0u8..84).collect(), vec![0xffu8; 111]];
        let cols = generate_trace(&msgs, 128);
        assert_eq!(check_trace(&cols), None);
        // the digest row carries the right bytes
        let d = sha512_block(&pad_single_block(b"abc"));
        for i in 0..8 { for j in 0..8 { assert_eq!(cols[COL_W + i * 8 + j][ROUND_ROWS], F::from_usize(word_bytes(d[i])[j] as usize)); } }
    }

    #[test]
    fn tampered_traces_are_caught() {
        let cols = generate_trace(&[b"abc".to_vec()], 32);
        // flip a message bit (row 1, w word 0, bit 5): schedule / rounds must break
        let mut t = cols.clone(); t[COL_W + 5][1] = F::ONE - t[COL_W + 5][1];
        assert!(check_trace(&t).is_some());
        // flip a final-hash byte
        let mut t = cols.clone(); t[COL_W + 3][ROUND_ROWS] += F::ONE;
        assert!(check_trace(&t).is_some());
        // KNOWN GAP (by design): a trace that starts mid-block (row 0 dropped) is NOT rejected by the AIR
        // alone — leanVM's shift is forward-only, so the first row has no predecessor to anchor it. The
        // spec closes it with the M3 buses: rows 0..2 must pull the message tuple, the digest row pushes
        // the hash, so a block without its row 0 leaves T1/T5 pushes unbalanced.
        let mut t: Vec<Vec<F>> = cols.iter().map(|c| c[1..].to_vec()).collect();
        for c in t.iter_mut() { c.push(F::ZERO); }
        assert_eq!(check_trace(&t), None);
    }
}
