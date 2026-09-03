//! Curve25519 in twisted-Edwards form (a = −1): constants and NATIVE affine arithmetic used by the
//! ed25519 tables' witness generation and tests (num-bigint; correctness over speed).

use crate::tables::ed25519::gadgets::*;

// ---- Curve25519 (twisted Edwards, a = −1) constants ----------------------------------------------
pub const D_LIMBS: [u8; 32] = [
    0xa3, 0x78, 0x59, 0x13, 0xca, 0x4d, 0xeb, 0x75, 0xab, 0xd8, 0x41, 0x41, 0x4d, 0x0a, 0x70, 0x00,
    0x98, 0xe8, 0x79, 0x77, 0x79, 0x40, 0xc7, 0x8c, 0x73, 0xfe, 0x6f, 0x2b, 0xee, 0x6c, 0x03, 0x52,
];
pub const BX_LIMBS: [u8; 32] = [
    0x1a, 0xd5, 0x25, 0x8f, 0x60, 0x2d, 0x56, 0xc9, 0xb2, 0xa7, 0x25, 0x95, 0x60, 0xc7, 0x2c, 0x69,
    0x5c, 0xdc, 0xd6, 0xfd, 0x31, 0xe2, 0xa4, 0xc0, 0xfe, 0x53, 0x6e, 0xcd, 0xd3, 0x36, 0x69, 0x21,
];
pub const BY_LIMBS: [u8; 32] = [
    0x58, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
    0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x66,
];

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Affine { pub x: [u8; 32], pub y: [u8; 32] }
pub const NEUTRAL: Affine = Affine { x: [0u8; 32], y: { let mut o = [0u8; 32]; o[0] = 1; o } };

/// Complete affine addition (native), the reference for the AIR.
pub fn affine_add(p: &Affine, q: &Affine) -> Affine {
    let m = &P_25519;
    let t1 = mod_mul(&p.x, &q.x, m); let t2 = mod_mul(&p.y, &q.y, m);
    let f = mod_mul(&t1, &t2, m); let g = mod_mul(&D_LIMBS, &f, m);
    let one = NEUTRAL.y;
    let num_x = mod_add(&mod_mul(&p.x, &q.y, m), &mod_mul(&q.x, &p.y, m), m);
    let num_y = mod_add(&t2, &t1, m);
    let x3 = mod_mul(&num_x, &mod_inv(&mod_add(&one, &g, m), m), m);
    let y3 = mod_mul(&num_y, &mod_inv(&mod_sub(&one, &g, m), m), m);
    Affine { x: x3, y: y3 }
}
pub fn is_on_curve(p: &Affine) -> bool {
    // −x² + y² = 1 + d x² y²
    let m = &P_25519;
    let x2 = mod_mul(&p.x, &p.x, m); let y2 = mod_mul(&p.y, &p.y, m);
    let lhs = mod_sub(&y2, &x2, m);
    let rhs = mod_add(&NEUTRAL.y, &mod_mul(&D_LIMBS, &mod_mul(&x2, &y2, m), m), m);
    lhs == rhs
}
pub fn scalar_mul_small(p: &Affine, k: u64) -> Affine { let mut acc = NEUTRAL; let mut base = *p; let mut k = k; while k > 0 { if k & 1 == 1 { acc = affine_add(&acc, &base); } base = affine_add(&base, &base); k >>= 1; } acc }


pub fn base_point() -> Affine { Affine { x: BX_LIMBS, y: BY_LIMBS } }
/// Pseudo-random on-curve points: small multiples of B (deterministic).
pub fn random_points(n: usize, seed: u64) -> Vec<Affine> {
    let b = base_point(); let mut s = seed; let mut out = vec![]; let mut cur = scalar_mul_small(&b, 1 + (seed % 97));
    for _ in 0..n { s ^= s << 13; s ^= s >> 7; s ^= s << 17; cur = affine_add(&cur, &scalar_mul_small(&b, 1 + (s % 1000))); out.push(cur); }
    out
}

