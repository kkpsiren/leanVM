//! Non-native field gadget (the spec's G8): identities over Z/M with 32 unsigned 8-bit limbs,
//! a hinted signed quotient (34 limbs, stored +128) and the SP1-style witness polynomial (64 limbs,
//! stored +2^15). Modulus-generic (p = 2^255−19 for curve arithmetic, L for scalars).
//!
//!   E(X) = Σ_k ±a_k(X)·b_k(X) + Σ_m ±c_m(X) − r(X) − q(X)·M(X)          (X ↔ 256)
//!   E(X) = (X − 256)·W'(X),  W'_i = W_i − 2^15                            (65 coefficient identities)
//!
//! Soundness (spec §4): with byte-bounded limbs, |q_i| < 2^7, |W'_i| < 2^15 and at most 3 products,
//! every coefficient identity holds over the integers, hence E(256) = 0, hence the relation mod M.
//! The range checks themselves are LogUp fractions attached at the table level; this module only
//! emits the arithmetic identities. Products must have byte-bounded operands: a negation is passed
//! as `sign = false`, never as `p − x` inside the identity.

use backend::*;
use num_bigint::{BigInt, Sign};
use num_integer::Integer;
use num_traits::{Signed, ToPrimitive, Zero};

pub const LIMBS: usize = 32;
pub const QL: usize = 34;
pub const WL: usize = 64;
pub const NV: usize = 65;
pub const Q_OFFSET: usize = 128;
pub const W_OFFSET: usize = 1 << 15;

pub const P_25519: [u8; 32] = { let mut p = [0xFFu8; 32]; p[0] = 0xED; p[31] = 0x7F; p };
/// L = 2^252 + 27742317777372353535851937790883648493 (little-endian)
pub const L_25519: [u8; 32] = [
    0xed, 0xd3, 0xf5, 0x5c, 0x1a, 0x63, 0x12, 0x58, 0xd6, 0x9c, 0xf7, 0xa2, 0xde, 0xf9, 0xde, 0x14,
    0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x10,
];

/// One identity's hint columns: `r` (result limbs; None for a zero-check), `q` (34, stored +128), `w` (64, stored +2^15).
pub struct HintCols<'a, T> { pub r: Option<&'a [T]>, pub q: &'a [T], pub w: &'a [T] }

/// Emit the 65 gated coefficient identities for Σ ±a·b + Σ ±c − r ≡ 0 (mod M).
#[allow(clippy::too_many_arguments)]
pub fn eval_identity<AB: AirBuilder>(
    builder: &mut AB,
    gate: &AB::IF,
    products: &[(&[AB::IF], &[AB::IF], bool)],
    linears: &[(&[AB::IF], bool)],
    hints: &HintCols<'_, AB::IF>,
    modulus: &[u8; 32],
) {
    assert!(products.len() <= 3, "at most 3 products keep W' within 16 bits");
    if builder.record_g8_identity(G8IdentityRecord { gate, products, linears, r: hints.r, q: hints.q, w: hints.w, modulus }) {
        return; // recorded structurally (recursion codegen): 65 placeholder constraints
    }
    let f = |x: usize| AB::F::from_usize(x);
    let q_off = AB::IF::from_usize(Q_OFFSET);
    let w_off = AB::IF::from_usize(W_OFFSET);
    let mut v: Vec<AB::IF> = (0..NV).map(|_| AB::IF::ZERO).collect();
    for (a, b, pos) in products {
        for j in 0..LIMBS { for k in 0..LIMBS { let t = a[j].clone() * b[k].clone(); if *pos { v[j + k] += t } else { v[j + k] -= t } } }
    }
    for (c, pos) in linears { for i in 0..LIMBS { if *pos { v[i] += c[i].clone() } else { v[i] -= c[i].clone() } } }
    if let Some(r) = hints.r { for i in 0..LIMBS { v[i] -= r[i].clone(); } }
    for j in 0..QL { let qj = hints.q[j].clone() - q_off.clone(); for k in 0..LIMBS { v[j + k] -= qj.clone() * f(modulus[k] as usize); } }
    for i in 0..NV {
        let w_prev = if i == 0 { AB::IF::ZERO } else { hints.w[i - 1].clone() - w_off.clone() };
        let w_cur = if i < WL { hints.w[i].clone() - w_off.clone() } else { AB::IF::ZERO };
        let c = v[i].clone() - w_prev + w_cur * f(256);
        builder.assert_zero(gate.clone() * c);
    }
}
pub const N_IDENTITY_CONSTRAINTS: usize = NV;

// ---------------------------------------------------------------------- native witness
pub fn limbs_to_int(limbs: &[u8]) -> BigInt { BigInt::from_bytes_le(Sign::Plus, limbs) }
pub fn int_to_limbs(x: &BigInt, n: usize) -> Vec<u8> { assert!(!x.is_negative()); let mut b = x.to_bytes_le().1; assert!(b.len() <= n, "value does not fit {n} limbs"); b.resize(n, 0); b }
pub fn modulus_int(m: &[u8; 32]) -> BigInt { limbs_to_int(m) }

pub struct IdentityWitness { pub r: [u8; 32], pub q: [u8; QL], pub w: [u16; WL] }

/// Like `make_identity` but operand limbs are i64 (not necessarily bytes): used for the lazy accumulator
/// reductions K ≡ K_red (mod L) where limbs reach ~2^21. The identity's coefficient bound must still keep
/// |W'| < 2^15 (asserted).
pub fn make_identity_wide(products: &[(&[i64], &[i64], bool)], linears: &[(&[i64], bool)], zero_check: bool, modulus: &[u8; 32]) -> IdentityWitness {
    let m = modulus_int(modulus);
    let to_int = |x: &[i64]| -> BigInt { let mut acc = BigInt::zero(); for (i, &l) in x.iter().enumerate() { acc += BigInt::from(l) << (8 * i); } acc };
    let mut e = BigInt::zero();
    for (a, b, pos) in products { let t = to_int(a) * to_int(b); if *pos { e += t } else { e -= t } }
    for (c, pos) in linears { let t = to_int(c); if *pos { e += t } else { e -= t } }
    let r_int = if zero_check { assert!((&e).mod_floor(&m).is_zero(), "zero-check operand is not 0 mod M"); BigInt::zero() } else { (&e).mod_floor(&m) };
    let q_int: BigInt = (&e - &r_int).div_floor(&m);
    let mut v = [0i64; NV];
    for (a, b, pos) in products { for j in 0..LIMBS { for k in 0..LIMBS { if *pos { v[j + k] += a[j] * b[k] } else { v[j + k] -= a[j] * b[k] } } } }
    for (c, pos) in linears { for i in 0..LIMBS { if *pos { v[i] += c[i] } else { v[i] -= c[i] } } }
    let r = int_to_limbs(&r_int, LIMBS);
    for i in 0..LIMBS { v[i] -= r[i] as i64; }
    let mut q = [0i64; QL];
    { let mut x = q_int.clone(); for qi in q.iter_mut() { let rem = (&x).mod_floor(&BigInt::from(256)); let mut d = rem.to_i64().unwrap(); if d > 127 { d -= 256; } *qi = d; x = (&x - BigInt::from(d)).div_floor(&BigInt::from(256)); } assert!(x.is_zero(), "quotient does not fit 34 signed limbs"); }
    for j in 0..QL { for k in 0..LIMBS { v[j + k] -= q[j] * modulus[k] as i64; } }
    let mut wp = [0i64; WL]; let mut prev = 0i64;
    for i in 0..NV { if i < WL { let num = prev - v[i]; assert_eq!(num % 256, 0, "V not divisible at {i}"); wp[i] = num / 256; prev = wp[i]; } else { assert_eq!(v[i], prev, "V(256) != 0"); } }
    let mut w = [0u16; WL];
    for i in 0..WL { let val = wp[i] + W_OFFSET as i64; assert!((0..65536).contains(&val), "W'_{i} = {} out of range", wp[i]); w[i] = val as u16; }
    let mut qo = [0u8; QL]; for j in 0..QL { qo[j] = (q[j] + Q_OFFSET as i64) as u8; }
    IdentityWitness { r: r.try_into().unwrap(), q: qo, w }
}

/// Native: given the operands (each as 32 byte-limbs), compute r = E mod M (unless a zero-check),
/// the signed quotient and the witness polynomial. Panics if the hint does not fit (a codec bug).
pub fn make_identity(products: &[(&[u8], &[u8], bool)], linears: &[(&[u8], bool)], zero_check: bool, modulus: &[u8; 32]) -> IdentityWitness {
    let m = modulus_int(modulus);
    let mut e = BigInt::zero();
    for (a, b, pos) in products { let t = limbs_to_int(a) * limbs_to_int(b); if *pos { e += t } else { e -= t } }
    for (c, pos) in linears { let t = limbs_to_int(c); if *pos { e += t } else { e -= t } }
    let r_int = if zero_check { assert!((&e).mod_floor(&m).is_zero(), "zero-check operand is not 0 mod M"); BigInt::zero() } else { (&e).mod_floor(&m) };
    let q_int: BigInt = (&e - &r_int).div_floor(&m);
    // coefficients V_i over Z from the limb representations
    let mut v = [0i64; NV];
    let bytes = |x: &[u8]| -> Vec<i64> { x.iter().map(|&b| b as i64).collect() };
    for (a, b, pos) in products { let (a, b) = (bytes(a), bytes(b)); for j in 0..LIMBS { for k in 0..LIMBS { if *pos { v[j + k] += a[j] * b[k] } else { v[j + k] -= a[j] * b[k] } } } }
    for (c, pos) in linears { let c = bytes(c); for i in 0..LIMBS { if *pos { v[i] += c[i] } else { v[i] -= c[i] } } }
    let r = int_to_limbs(&r_int, LIMBS);
    for i in 0..LIMBS { v[i] -= r[i] as i64; }
    // signed q limbs in [-128, 127]
    let mut q = [0i64; QL];
    { let mut x = q_int.clone(); for qi in q.iter_mut() { let rem = (&x).mod_floor(&BigInt::from(256)); let mut d = rem.to_i64().unwrap(); if d > 127 { d -= 256; } *qi = d; x = (&x - BigInt::from(d)).div_floor(&BigInt::from(256)); } assert!(x.is_zero(), "quotient does not fit 34 signed limbs"); }
    for j in 0..QL { for k in 0..LIMBS { v[j + k] -= q[j] * modulus[k] as i64; } }
    // synthetic division by (X − 256)
    let mut wp = [0i64; WL]; let mut prev = 0i64;
    for i in 0..NV { if i < WL { let num = prev - v[i]; assert_eq!(num % 256, 0, "V not divisible at {i}"); wp[i] = num / 256; prev = wp[i]; } else { assert_eq!(v[i], prev, "V(256) != 0"); } }
    let mut w = [0u16; WL];
    for i in 0..WL { let val = wp[i] + W_OFFSET as i64; assert!((0..65536).contains(&val), "W'_{i} = {} out of range", wp[i]); w[i] = val as u16; }
    let mut qo = [0u8; QL]; for j in 0..QL { qo[j] = (q[j] + Q_OFFSET as i64) as u8; }
    IdentityWitness { r: r.try_into().unwrap(), q: qo, w }
}

/// Modular helpers for witness generation.
pub fn mod_mul(a: &[u8], b: &[u8], m: &[u8; 32]) -> [u8; 32] { int_to_limbs(&((limbs_to_int(a) * limbs_to_int(b)).mod_floor(&modulus_int(m))), 32).try_into().unwrap() }
pub fn mod_add(a: &[u8], b: &[u8], m: &[u8; 32]) -> [u8; 32] { int_to_limbs(&((limbs_to_int(a) + limbs_to_int(b)).mod_floor(&modulus_int(m))), 32).try_into().unwrap() }
pub fn mod_sub(a: &[u8], b: &[u8], m: &[u8; 32]) -> [u8; 32] { int_to_limbs(&((limbs_to_int(a) - limbs_to_int(b)).mod_floor(&modulus_int(m))), 32).try_into().unwrap() }
pub fn mod_inv(a: &[u8], m: &[u8; 32]) -> [u8; 32] {
    // p = 2^255 - 19 (every current caller): fixed-width Fermat inversion, the same a^(p-2) mod p in
    // canonical form, without BigInt allocations. Any other modulus keeps the generic path.
    if *m == P_25519 && a.len() == 32 {
        let fast = fe25519::invert_bytes(a.try_into().unwrap());
        debug_assert_eq!(fast, mod_inv_bigint(a, m), "fe25519 inversion disagrees with the BigInt reference");
        return fast;
    }
    mod_inv_bigint(a, m)
}

/// Reference inversion (Fermat a^(m-2) mod m over BigInt); also the check for [`fe25519`].
pub fn mod_inv_bigint(a: &[u8], m: &[u8; 32]) -> [u8; 32] {
    let mi = modulus_int(m); let ai = limbs_to_int(a).mod_floor(&mi);
    let e = &mi - BigInt::from(2); // Fermat: a^(m-2)
    int_to_limbs(&ai.modpow(&e, &mi), 32).try_into().unwrap()
}

/// Arithmetic mod p = 2^255 - 19 in radix 2^51 (five u64 limbs, u128 products), only what the
/// witness generator's inversion needs. Witness-side only: it computes exactly the value the BigInt
/// Fermat path computes (the inverse mod p is unique; 0 maps to 0), so traces are unchanged.
mod fe25519 {
    const MASK: u64 = (1u64 << 51) - 1;

    /// Limbs are kept below 2^52 between operations.
    #[derive(Clone, Copy)]
    struct Fe([u64; 5]);

    /// Little-endian 32 bytes (any value below 2^256) to a field element (reduced mod p lazily).
    fn from_bytes(b: &[u8; 32]) -> Fe {
        let w = |i: usize| u64::from_le_bytes(b[8 * i..8 * i + 8].try_into().unwrap());
        let (w0, w1, w2, w3) = (w(0), w(1), w(2), w(3));
        let l0 = w0 & MASK;
        let l1 = ((w0 >> 51) | (w1 << 13)) & MASK;
        let l2 = ((w1 >> 38) | (w2 << 26)) & MASK;
        let l3 = ((w2 >> 25) | (w3 << 39)) & MASK;
        let l4 = (w3 >> 12) & MASK; // bits 204..=254
        // bit 255: 2^255 = 19 (mod p)
        Fe([l0 + 19 * (w3 >> 63), l1, l2, l3, l4])
    }

    fn mul(a: &Fe, b: &Fe) -> Fe {
        let (a, b) = (&a.0, &b.0);
        let m = |x: u64, y: u64| (x as u128) * (y as u128);
        let (b1_19, b2_19, b3_19, b4_19) = (b[1] * 19, b[2] * 19, b[3] * 19, b[4] * 19);
        let c0 = m(a[0], b[0]) + m(a[4], b1_19) + m(a[3], b2_19) + m(a[2], b3_19) + m(a[1], b4_19);
        let mut c1 = m(a[1], b[0]) + m(a[0], b[1]) + m(a[4], b2_19) + m(a[3], b3_19) + m(a[2], b4_19);
        let mut c2 = m(a[2], b[0]) + m(a[1], b[1]) + m(a[0], b[2]) + m(a[4], b3_19) + m(a[3], b4_19);
        let mut c3 = m(a[3], b[0]) + m(a[2], b[1]) + m(a[1], b[2]) + m(a[0], b[3]) + m(a[4], b4_19);
        let mut c4 = m(a[4], b[0]) + m(a[3], b[1]) + m(a[2], b[2]) + m(a[1], b[3]) + m(a[0], b[4]);
        let mask = MASK as u128;
        c1 += c0 >> 51;
        c2 += c1 >> 51;
        c3 += c2 >> 51;
        c4 += c3 >> 51;
        // fold 2^255 = 19 back in (all in u128: no overflow for limbs below 2^52)
        let t0 = (c0 & mask) + (c4 >> 51) * 19;
        let r1 = (c1 & mask) + (t0 >> 51);
        Fe([(t0 & mask) as u64, r1 as u64, (c2 & mask) as u64, (c3 & mask) as u64, (c4 & mask) as u64])
    }

    fn sq_n(a: &Fe, n: usize) -> Fe {
        let mut x = *a;
        for _ in 0..n {
            x = mul(&x, &x);
        }
        x
    }

    /// Canonical little-endian bytes (value fully reduced into [0, p)).
    fn to_bytes(a: &Fe) -> [u8; 32] {
        // weak reduction: limbs < 2^51 except limb 0 < 2^51 + 19·2^13
        let mut l = a.0;
        let c = [l[0] >> 51, l[1] >> 51, l[2] >> 51, l[3] >> 51, l[4] >> 51];
        l[0] = (l[0] & MASK) + c[4] * 19;
        l[1] = (l[1] & MASK) + c[0];
        l[2] = (l[2] & MASK) + c[1];
        l[3] = (l[3] & MASK) + c[2];
        l[4] = (l[4] & MASK) + c[3];
        // now value < 2p: q = 1 iff value >= p
        let mut q = (l[0] + 19) >> 51;
        q = (l[1] + q) >> 51;
        q = (l[2] + q) >> 51;
        q = (l[3] + q) >> 51;
        q = (l[4] + q) >> 51;
        l[0] += 19 * q;
        l[1] += l[0] >> 51;
        l[0] &= MASK;
        l[2] += l[1] >> 51;
        l[1] &= MASK;
        l[3] += l[2] >> 51;
        l[2] &= MASK;
        l[4] += l[3] >> 51;
        l[3] &= MASK;
        l[4] &= MASK; // drops 2^255, i.e. subtracts p together with the +19 above
        let w0 = l[0] | (l[1] << 51);
        let w1 = (l[1] >> 13) | (l[2] << 38);
        let w2 = (l[2] >> 26) | (l[3] << 25);
        let w3 = (l[3] >> 39) | (l[4] << 12);
        let mut out = [0u8; 32];
        out[0..8].copy_from_slice(&w0.to_le_bytes());
        out[8..16].copy_from_slice(&w1.to_le_bytes());
        out[16..24].copy_from_slice(&w2.to_le_bytes());
        out[24..32].copy_from_slice(&w3.to_le_bytes());
        out
    }

    /// a^(p-2) mod p, p - 2 = 2^255 - 21 (the ref10 addition chain: 254 squarings, 11 products).
    pub(super) fn invert_bytes(a: &[u8; 32]) -> [u8; 32] {
        let z = from_bytes(a);
        let z2 = mul(&z, &z); // 2
        let z8 = sq_n(&z2, 2); // 8
        let z9 = mul(&z, &z8); // 9
        let z11 = mul(&z2, &z9); // 11
        let z22 = mul(&z11, &z11); // 22
        let z_5_0 = mul(&z9, &z22); // 2^5 - 1
        let z_10_0 = mul(&sq_n(&z_5_0, 5), &z_5_0); // 2^10 - 1
        let z_20_0 = mul(&sq_n(&z_10_0, 10), &z_10_0); // 2^20 - 1
        let z_40_0 = mul(&sq_n(&z_20_0, 20), &z_20_0); // 2^40 - 1
        let z_50_0 = mul(&sq_n(&z_40_0, 10), &z_10_0); // 2^50 - 1
        let z_100_0 = mul(&sq_n(&z_50_0, 50), &z_50_0); // 2^100 - 1
        let z_200_0 = mul(&sq_n(&z_100_0, 100), &z_100_0); // 2^200 - 1
        let z_250_0 = mul(&sq_n(&z_200_0, 50), &z_50_0); // 2^250 - 1
        let r = mul(&sq_n(&z_250_0, 5), &z11); // 2^255 - 32 + 11 = 2^255 - 21
        to_bytes(&r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{EF, F};

    struct Dbg { flat: Vec<F>, idx: usize, fails: Vec<usize> }
    impl AirBuilder for Dbg {
        type F = F; type IF = F; type EF = EF;
        fn flat(&self) -> &[F] { &self.flat }
        fn shift(&self) -> &[F] { &[] }
        fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.fails.push(self.idx); } self.idx += 1; }
        fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.fails.push(self.idx); } self.idx += 1; }
    }
    fn fv(x: &[u8]) -> Vec<F> { x.iter().map(|&b| F::from_usize(b as usize)).collect() }
    fn fw(x: &[u16]) -> Vec<F> { x.iter().map(|&b| F::from_usize(b as usize)).collect() }
    fn rnd(seed: &mut u64) -> [u8; 32] { let mut o = [0u8; 32]; for b in o.iter_mut() { *seed ^= *seed << 13; *seed ^= *seed >> 7; *seed ^= *seed << 17; *b = (*seed >> 24) as u8; } o }

    #[test]
    fn three_product_identity_holds_and_breaks() {
        let mut seed = 42u64;
        for modulus in [P_25519, L_25519] {
            for _ in 0..20 {
                let (a, b, c, d, e, g) = (rnd(&mut seed), rnd(&mut seed), rnd(&mut seed), rnd(&mut seed), rnd(&mut seed), rnd(&mut seed));
                // r ≡ a·b − c·d + e·g + a − b   (weight 3, mixed signs)
                let wit = make_identity(&[(&a, &b, true), (&c, &d, false), (&e, &g, true)], &[(&a, true), (&b, false)], false, &modulus);
                let expect = { let m = modulus_int(&modulus); ((limbs_to_int(&a) * limbs_to_int(&b) - limbs_to_int(&c) * limbs_to_int(&d) + limbs_to_int(&e) * limbs_to_int(&g) + limbs_to_int(&a) - limbs_to_int(&b)).mod_floor(&m)) };
                assert_eq!(limbs_to_int(&wit.r), expect);
                let (af, bf, cf, df, ef, gf, rf, qf, wf) = (fv(&a), fv(&b), fv(&c), fv(&d), fv(&e), fv(&g), fv(&wit.r), fv(&wit.q), fw(&wit.w));
                let mut dbg = Dbg { flat: vec![], idx: 0, fails: vec![] };
                eval_identity(&mut dbg, &F::ONE, &[(&af, &bf, true), (&cf, &df, false), (&ef, &gf, true)], &[(&af, true), (&bf, false)], &HintCols { r: Some(&rf), q: &qf, w: &wf }, &modulus);
                assert_eq!(dbg.idx, N_IDENTITY_CONSTRAINTS);
                assert!(dbg.fails.is_empty(), "honest identity failed at {:?}", dbg.fails);
                // tamper r
                let mut rt = rf.clone(); rt[3] += F::ONE;
                let mut dbg = Dbg { flat: vec![], idx: 0, fails: vec![] };
                eval_identity(&mut dbg, &F::ONE, &[(&af, &bf, true), (&cf, &df, false), (&ef, &gf, true)], &[(&af, true), (&bf, false)], &HintCols { r: Some(&rt), q: &qf, w: &wf }, &modulus);
                assert!(!dbg.fails.is_empty());
            }
        }
    }

    #[test]
    fn fe25519_inverse_matches_bigint_reference() {
        let p = P_25519;
        let from_u64 = |x: u64| { let mut o = [0u8; 32]; o[..8].copy_from_slice(&x.to_le_bytes()); o };
        let add_small = |a: [u8; 32], k: u64| -> [u8; 32] { int_to_limbs(&((limbs_to_int(&a) + BigInt::from(k)) % BigInt::from(2u8).pow(256)), 32).try_into().unwrap() };
        let sub_small = |a: [u8; 32], k: u64| -> [u8; 32] { int_to_limbs(&(limbs_to_int(&a) - BigInt::from(k)), 32).try_into().unwrap() };
        let mut edge: Vec<[u8; 32]> = vec![[0u8; 32], [0xFFu8; 32], from_u64(1), from_u64(2), from_u64(19), from_u64(u64::MAX), p, add_small(p, 1), add_small(p, 2), sub_small(p, 1), sub_small(p, 2)];
        let mut top = [0u8; 32]; top[31] = 0x80; edge.push(top); edge.push(add_small(top, 1)); edge.push(sub_small(top, 1));
        edge.push(add_small(add_small(p, 0), 0x7FFF_FFFF)); // p + small multiple region
        let two_p: [u8; 32] = int_to_limbs(&(limbs_to_int(&p) * BigInt::from(2u8)), 32).try_into().unwrap();
        edge.extend([two_p, add_small(two_p, 1), sub_small(two_p, 1)]);
        let mut seed = 0x9E37_79B9_7F4A_7C15u64;
        for _ in 0..2000 { edge.push(rnd(&mut seed)); }
        for a in edge {
            let fast = fe25519::invert_bytes(&a);
            assert_eq!(fast, mod_inv_bigint(&a, &p), "inverse mismatch for {a:?}");
            assert_eq!(mod_inv(&a, &p), fast);
        }
        // the non-p modulus keeps the reference path
        let a = rnd(&mut seed);
        assert_eq!(mod_inv(&a, &L_25519), mod_inv_bigint(&a, &L_25519));
    }

    #[test]
    fn zero_check_and_inverse() {
        let mut seed = 7u64;
        let a = rnd(&mut seed); let a = { let mut a = a; a[31] &= 0x7f; a }; // < 2^255
        let inv = mod_inv(&a, &P_25519);
        // a · inv − 1 ≡ 0 (zero-check)
        let one = { let mut o = [0u8; 32]; o[0] = 1; o };
        let wit = make_identity(&[(&a, &inv, true)], &[(&one, false)], true, &P_25519);
        let mut dbg = Dbg { flat: vec![], idx: 0, fails: vec![] };
        eval_identity(&mut dbg, &F::ONE, &[(&fv(&a), &fv(&inv), true)], &[(&fv(&one), false)], &HintCols { r: None, q: &fv(&wit.q), w: &fw(&wit.w) }, &P_25519);
        assert!(dbg.fails.is_empty());
    }
}
