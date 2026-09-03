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
    debug_assert!(products.len() <= 3, "at most 3 products keep W' within 16 bits");
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
    let mi = modulus_int(m); let ai = limbs_to_int(a).mod_floor(&mi);
    let e = &mi - BigInt::from(2); // Fermat: a^(m-2)
    int_to_limbs(&ai.modpow(&e, &mi), 32).try_into().unwrap()
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
