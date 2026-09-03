//! T6 `DecompressA` and T7 `SignerScalar` (spec §3.5), standalone.
//!
//! T6 — one row per distinct signer, a mirror of curve25519-dalek `decompress`:
//!   y      = A with bit 255 cleared (UNREDUCED, may be ≥ p: dalek's from_bytes does not reduce)
//!   sign   = bit 255 of A
//!   t ≡ y·y,  v ≡ d·t,  w ≡ x_can·x_can,   w·(1+v) − (t−1) ≡ 0   (x_can² = (y²−1)/(1+d·y²))
//!   x_can < p (borrow chain), lsb(x_can) = 0 (the even root, sqrt_ratio_i's convention)
//!   A.x    = sign ? p − x_can : x_can   (exact borrow chain, selected)
//!   y_can  = y − p·ge with ge boolean: ge=1 ⇒ exact y − p; ge=0 ⇒ y_can = y and y < p
//! Outputs (A.x, y_can) are what T1(kind=1) compares with P = 8Q' (integration).
//!
//! T7 — one row per signer (and one for the leaf's S): K (32 limbs, each < 2^21, the lazy sum from
//! T4) reduced K_red ≡ K (mod L) with the wide-limb identity, K_red as 253 bits, 26 signed 10-bit
//! windows (recoding as in T4). The window routing pushes are attached in the integration.

use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Zero;

use crate::edadd::D_LIMBS;
use crate::gadgets::*;

// ===================================================================================== T6
pub const T6_COL_A: usize = 0;           // 32 raw key bytes
pub const T6_COL_H: usize = 32;          // 1: low 7 bits of byte 31
pub const T6_COL_SIGN: usize = 33;       // 1
pub const T6_COL_T: usize = 34;          // 130
pub const T6_COL_V: usize = 164;         // 130
pub const T6_COL_XCAN: usize = 294;      // 32
pub const T6_COL_W: usize = 326;         // 130
pub const T6_COL_OC: usize = 456;        // 98
pub const T6_COL_XLT: usize = 554;       // 64: (p−1) − x_can
pub const T6_COL_HX: usize = 618;        // 1: x_can[0] = 2·hx
pub const T6_COL_AX: usize = 619;        // 32
pub const T6_COL_NEG: usize = 651;       // 32 borrows for p − x_can (used when sign=1)
pub const T6_COL_GE: usize = 683;        // 1
pub const T6_COL_YCAN: usize = 684;      // 32
pub const T6_COL_YB: usize = 716;        // 32 borrows: y − p (ge=1)
pub const T6_COL_YLT: usize = 748;       // 64: (p−1) − y (ge=0)
pub const T6_N_COLS: usize = 812;

#[derive(Debug, Clone, Copy, Default)]
pub struct DecompressAir;
impl Air for DecompressAir {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 3 }
    fn n_columns(&self) -> usize { T6_N_COLS }
    fn n_shift_columns(&self) -> usize { 0 }
    fn n_constraints(&self) -> usize { T6_N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let one = AB::IF::ONE; let f = |x: usize| AB::F::from_usize(x);
        let sl = |b: usize, n: usize| -> Vec<AB::IF> { c[b..b + n].to_vec() };
        let hints = |base: usize| -> HintCols<'_, AB::IF> { HintCols { r: None, q: &c[base..base + QL], w: &c[base + QL..base + QL + WL] } };
        let hints_r = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };
        let d: Vec<AB::IF> = D_LIMBS.iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        let one_limbs: Vec<AB::IF> = (0..32).map(|i| if i == 0 { one.clone() } else { AB::IF::ZERO }).collect();
        let a = sl(T6_COL_A, 32);
        let (h, sign) = (c[T6_COL_H].clone(), c[T6_COL_SIGN].clone());
        builder.assert_bool(sign.clone());
        builder.assert_zero(a[31].clone() - h.clone() - sign.clone() * f(128));            // byte 31 = h + 128·sign (h 7-bit: range section)
        let y: Vec<AB::IF> = (0..32).map(|i| if i < 31 { a[i].clone() } else { h.clone() }).collect();
        let (t, ht) = hints_r(T6_COL_T); eval_identity(builder, &one, &[(&y, &y, true)], &[], &ht, &P_25519);
        let (v, hv) = hints_r(T6_COL_V); eval_identity(builder, &one, &[(&d, &t, true)], &[], &hv, &P_25519);
        let xcan = sl(T6_COL_XCAN, 32);
        let (w, hw) = hints_r(T6_COL_W); eval_identity(builder, &one, &[(&xcan, &xcan, true)], &[], &hw, &P_25519);
        // w·(1+v) − (t − 1) ≡ 0  ⇔  w·v + w − t + 1 ≡ 0
        eval_identity(builder, &one, &[(&w, &v, true)], &[(&w, true), (&t, false), (&one_limbs, true)], &hints(T6_COL_OC), &P_25519);
        // x_can < p
        let p_limbs: Vec<usize> = P_25519.iter().map(|&b| b as usize).collect();
        { let diff = sl(T6_COL_XLT, 32); let bw = sl(T6_COL_XLT + 32, 32);
          for i in 0..32 { let pm1 = if i == 0 { p_limbs[0] - 1 } else { p_limbs[i] }; let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(AB::IF::from_usize(pm1) - xcan[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256)); builder.assert_bool(bw[i].clone()); }
          builder.assert_zero(bw[31].clone()); }
        // even root
        builder.assert_zero(xcan[0].clone() - c[T6_COL_HX].clone().double());
        // A.x = sign ? p − x_can : x_can   — gate: sign·(p_i − x_i − prev − ax_i + 256·b_i) = 0 and (1−sign)·(ax_i − x_i) = 0
        let ax = sl(T6_COL_AX, 32); let nb = sl(T6_COL_NEG, 32);
        for i in 0..32 {
            let prev = if i == 0 { AB::IF::ZERO } else { nb[i - 1].clone() };
            builder.assert_zero(sign.clone() * (AB::IF::from_usize(p_limbs[i]) - xcan[i].clone() - prev - ax[i].clone() + nb[i].clone() * f(256)));
            builder.assert_zero((one.clone() - sign.clone()) * (ax[i].clone() - xcan[i].clone()));
            builder.assert_bool(nb[i].clone());
        }
        builder.assert_zero(nb[31].clone());
        // y_can
        let ge = c[T6_COL_GE].clone(); builder.assert_bool(ge.clone());
        let ycan = sl(T6_COL_YCAN, 32); let yb = sl(T6_COL_YB, 32);
        for i in 0..32 {
            let prev = if i == 0 { AB::IF::ZERO } else { yb[i - 1].clone() };
            builder.assert_zero(ge.clone() * (y[i].clone() - AB::IF::from_usize(p_limbs[i]) - prev - ycan[i].clone() + yb[i].clone() * f(256)));
            builder.assert_zero((one.clone() - ge.clone()) * (ycan[i].clone() - y[i].clone()));
            builder.assert_bool(yb[i].clone());
        }
        builder.assert_zero(ge.clone() * yb[31].clone());
        { let diff = sl(T6_COL_YLT, 32); let bw = sl(T6_COL_YLT + 32, 32);
          for i in 0..32 { let pm1 = if i == 0 { p_limbs[0] - 1 } else { p_limbs[i] }; let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero((one.clone() - ge.clone()) * (AB::IF::from_usize(pm1) - y[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256))); builder.assert_bool(bw[i].clone()); }
          builder.assert_zero((one.clone() - ge.clone()) * bw[31].clone()); }
    }
}
pub const T6_N_CONSTRAINTS: usize = 2 + 4 * 65 + 65 + 1 + 97 + 1 + 97 + 65;

pub struct DecompressWitness { pub row: [F; T6_N_COLS], pub ax: [u8; 32], pub ycan: [u8; 32] }
/// Build the T6 row for a compressed key A (bytes). Returns the decompressed (A.x, y_can). Panics if A is not a valid encoding.
pub fn make_decompress_row(a: &[u8; 32]) -> DecompressWitness {
    let m = &P_25519; let fu = |b: u8| F::from_usize(b as usize);
    let mut row = [F::ZERO; T6_N_COLS];
    for i in 0..32 { row[T6_COL_A + i] = fu(a[i]); }
    let sign = a[31] >> 7; let h = a[31] & 0x7f;
    row[T6_COL_H] = fu(h); row[T6_COL_SIGN] = fu(sign);
    let mut y = *a; y[31] = h;
    let put_r = |row: &mut [F; T6_N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
    let put_z = |row: &mut [F; T6_N_COLS], base: usize, w: &IdentityWitness| { for i in 0..QL { row[base + i] = fu(w.q[i]); } for i in 0..WL { row[base + QL + i] = F::from_usize(w.w[i] as usize); } };
    let t = mod_mul(&y, &y, m); put_r(&mut row, T6_COL_T, &make_identity(&[(&y, &y, true)], &[], false, m));
    let v = mod_mul(&D_LIMBS, &t, m); put_r(&mut row, T6_COL_V, &make_identity(&[(&D_LIMBS, &t, true)], &[], false, m));
    // x² = (t − 1)/(1 + v) ; sqrt via p ≡ 5 mod 8
    let one = { let mut o = [0u8; 32]; o[0] = 1; o };
    let num = mod_sub(&t, &one, m); let den = mod_add(&one, &v, m);
    let x2 = mod_mul(&num, &mod_inv(&den, m), m);
    let x = sqrt_mod_p(&x2).expect("A is not a valid point encoding");
    let xcan = if x[0] & 1 == 0 { x } else { mod_sub(&[0u8; 32], &x, m) };
    for i in 0..32 { row[T6_COL_XCAN + i] = fu(xcan[i]); }
    put_r(&mut row, T6_COL_W, &make_identity(&[(&xcan, &xcan, true)], &[], false, m));
    let w = mod_mul(&xcan, &xcan, m);
    put_z(&mut row, T6_COL_OC, &make_identity(&[(&w, &v, true)], &[(&w, true), (&t, false), (&one, true)], true, m));
    let borrow_chain = |row: &mut [F; T6_N_COLS], base: usize, minuend: &[i32; 32], sub: &[u8; 32]| { let mut bw = 0i32; for i in 0..32 { let mut d = minuend[i] - sub[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } row[base + i] = fu(d as u8); row[base + 32 + i] = fu(bw as u8); } assert_eq!(bw, 0); };
    let pm1: [i32; 32] = std::array::from_fn(|i| if i == 0 { P_25519[0] as i32 - 1 } else { P_25519[i] as i32 });
    borrow_chain(&mut row, T6_COL_XLT, &pm1, &xcan);
    row[T6_COL_HX] = fu(xcan[0] >> 1);
    let ax = if sign == 1 { let mut bw = 0i32; let mut out = [0u8; 32]; for i in 0..32 { let mut d = P_25519[i] as i32 - xcan[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } out[i] = d as u8; row[T6_COL_NEG + i] = fu(bw as u8); } assert_eq!(bw, 0); out } else { xcan };
    for i in 0..32 { row[T6_COL_AX + i] = fu(ax[i]); }
    let ge = limbs_to_int(&y) >= modulus_int(m);
    row[T6_COL_GE] = F::from_bool(ge);
    let ycan = if ge { let mut bw = 0i32; let mut out = [0u8; 32]; for i in 0..32 { let mut d = y[i] as i32 - P_25519[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } out[i] = d as u8; row[T6_COL_YB + i] = fu(bw as u8); } assert_eq!(bw, 0); out } else { borrow_chain(&mut row, T6_COL_YLT, &pm1, &y); y };
    for i in 0..32 { row[T6_COL_YCAN + i] = fu(ycan[i]); }
    DecompressWitness { row, ax, ycan }
}
/// sqrt in F_p with p ≡ 5 (mod 8) (Tonelli-style with the 2^((p−1)/4) twist); None if not a square.
pub fn sqrt_mod_p(a: &[u8; 32]) -> Option<[u8; 32]> {
    let m = modulus_int(&P_25519); let ai = limbs_to_int(a).mod_floor(&m);
    if ai.is_zero() { return Some([0u8; 32]); }
    let e = (&m + BigInt::from(3)) >> 3usize;
    let mut r = ai.modpow(&e, &m);
    if (&r * &r).mod_floor(&m) != ai {
        let i = BigInt::from(2).modpow(&((&m - BigInt::from(1)) >> 2usize), &m);
        r = (r * i).mod_floor(&m);
        if (&r * &r).mod_floor(&m) != ai { return None; }
    }
    Some(int_to_limbs(&r, 32).try_into().unwrap())
}

// ===================================================================================== T7
pub const T7_COL_K: usize = 0;           // 32 wide limbs (< 2^21)
pub const T7_COL_KRED: usize = 32;       // 130
pub const T7_COL_BITS: usize = 162;      // 253
pub const T7_WINDOWS: usize = 26;
pub const T7_COL_M: usize = 415;         // 26
pub const T7_COL_SGN: usize = 441;
pub const T7_COL_BRW: usize = 467;
pub const T7_COL_INV: usize = 493;
pub const T7_COL_NZ: usize = 519;
pub const T7_N_COLS: usize = 545;

#[derive(Debug, Clone, Copy, Default)]
pub struct SignerScalarAir;
impl Air for SignerScalarAir {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 3 }
    fn n_columns(&self) -> usize { T7_N_COLS }
    fn n_shift_columns(&self) -> usize { 0 }
    fn n_constraints(&self) -> usize { T7_N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let one = AB::IF::ONE; let f = |x: usize| AB::F::from_usize(x);
        let k: Vec<AB::IF> = c[T7_COL_K..T7_COL_K + 32].to_vec();
        let hk = HintCols { r: Some(&c[T7_COL_KRED..T7_COL_KRED + 32]), q: &c[T7_COL_KRED + 32..T7_COL_KRED + 32 + QL], w: &c[T7_COL_KRED + 66..T7_COL_KRED + 66 + WL] };
        eval_identity(builder, &one, &[], &[(&k, true)], &hk, &L_25519);
        let kred: Vec<AB::IF> = c[T7_COL_KRED..T7_COL_KRED + 32].to_vec();
        let bits: Vec<AB::IF> = c[T7_COL_BITS..T7_COL_BITS + 253].to_vec();
        for b in &bits { builder.assert_bool(b.clone()); }
        // bits recompose K_red's bytes
        for i in 0..32 { let mut acc = AB::IF::ZERO; for t in 0..8 { let bi = 8 * i + t; if bi < 253 { acc += bits[bi].clone() * f(1 << t); } } builder.assert_zero(kred[i].clone() - acc); }
        let window = |j: usize| -> AB::IF { let mut acc = AB::IF::ZERO; for t in 0..10 { let i = 10 * j + t; if i < 253 { acc += bits[i].clone() * f(1 << t); } } acc };
        for j in 0..T7_WINDOWS {
            let (m, s, b, inv, nz) = (c[T7_COL_M + j].clone(), c[T7_COL_SGN + j].clone(), c[T7_COL_BRW + j].clone(), c[T7_COL_INV + j].clone(), c[T7_COL_NZ + j].clone());
            let b_prev = if j == 0 { AB::IF::ZERO } else { c[T7_COL_BRW + j - 1].clone() };
            builder.assert_bool(s.clone()); builder.assert_bool(b.clone()); builder.assert_bool(nz.clone());
            builder.assert_zero(window(j) + b_prev - (one.clone() - s.double()) * m.clone() - b.clone() * f(1024));
            builder.assert_zero(m.clone() * inv - nz.clone());
            builder.assert_zero((one.clone() - nz) * m);
        }
        builder.assert_zero(c[T7_COL_BRW + T7_WINDOWS - 1].clone());
    }
}
pub const T7_N_CONSTRAINTS: usize = 65 + 253 + 32 + 26 * 6 + 1;

pub fn make_signer_scalar_row(k_wide: &[i64; 32]) -> ([F; T7_N_COLS], [u8; 32]) {
    let mut row = [0; 0].map(|_: u8| F::ZERO).to_vec(); row.resize(T7_N_COLS, F::ZERO);
    let mut row: [F; T7_N_COLS] = row.try_into().unwrap();
    for i in 0..32 { assert!(k_wide[i] >= 0 && k_wide[i] < (1 << 21)); row[T7_COL_K + i] = F::from_usize(k_wide[i] as usize); }
    let w = make_identity_wide(&[], &[(k_wide, true)], false, &L_25519);
    for i in 0..32 { row[T7_COL_KRED + i] = F::from_usize(w.r[i] as usize); } for i in 0..QL { row[T7_COL_KRED + 32 + i] = F::from_usize(w.q[i] as usize); } for i in 0..WL { row[T7_COL_KRED + 66 + i] = F::from_usize(w.w[i] as usize); }
    let kred = limbs_to_int(&w.r);
    for i in 0..253 { row[T7_COL_BITS + i] = F::from_bool(((&kred >> i) & BigInt::from(1)) == BigInt::from(1)); }
    let mut borrow = 0i64;
    for j in 0..T7_WINDOWS { let wv: i64 = ((&kred >> (10 * j)) & BigInt::from(1023)).try_into().unwrap(); let wv = wv + borrow; let (m, sgn, b) = if wv > 512 { (1024 - wv, 1, 1) } else { (wv, 0, 0) }; borrow = b; row[T7_COL_M + j] = F::from_usize(m as usize); row[T7_COL_SGN + j] = F::from_usize(sgn as usize); row[T7_COL_BRW + j] = F::from_usize(b as usize); row[T7_COL_NZ + j] = F::from_bool(m != 0); row[T7_COL_INV + j] = if m != 0 { F::from_usize(m as usize).inverse() } else { F::ZERO }; }
    assert_eq!(borrow, 0, "window 25 has 3 bits: no final borrow");
    (row, w.r)
}

pub struct Dbg<'a> { pub flat: &'a [F], pub idx: usize, pub failures: Vec<usize> }
impl<'a> AirBuilder for Dbg<'a> {
    type F = F; type IF = F; type EF = EF;
    fn flat(&self) -> &[F] { self.flat }
    fn shift(&self) -> &[F] { &[] }
    fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.failures.push(self.idx); } self.idx += 1; }
    fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.failures.push(self.idx); } self.idx += 1; }
}
pub fn check_row<A: Air<ExtraData = ExtraDataForBuses<EF>>>(air: &A, row: &[F], expected: usize) -> Option<usize> {
    let mut b = Dbg { flat: row, idx: 0, failures: vec![] }; air.eval(&mut b, &ExtraDataForBuses::new(&[], vec![])); assert_eq!(b.idx, expected, "constraint count: counted {}", b.idx); b.failures.first().copied()
}
pub fn rows_to_cols<const N: usize>(rows: &[[F; N]], n_rows: usize) -> Vec<Vec<F>> { let mut cols: Vec<Vec<F>> = (0..N).map(|_| vec![F::ZERO; n_rows]).collect(); for (r, row) in rows.iter().enumerate() { for c in 0..N { cols[c][r] = row[c]; } } for r in rows.len()..n_rows { for c in 0..N { cols[c][r] = rows[rows.len() - 1][c]; } } cols }

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edadd::{Affine, base_point, is_on_curve, random_points};
    fn compress(p: &Affine) -> [u8; 32] { let mut a = p.y; a[31] |= (p.x[0] & 1) << 7; a }
    #[test]
    fn decompress_matches_points_and_rejects_tampering() {
        for p in random_points(8, 21).iter().chain(std::iter::once(&base_point())) {
            let a = compress(p);
            let w = make_decompress_row(&a);
            assert_eq!(check_row(&DecompressAir, &w.row, T6_N_CONSTRAINTS), None);
            assert_eq!(w.ax, p.x); assert_eq!(w.ycan, p.y); assert!(is_on_curve(&Affine { x: w.ax, y: w.ycan }));
            let mut t = w.row; t[T6_COL_AX + 3] += F::ONE; assert!(check_row(&DecompressAir, &t, T6_N_CONSTRAINTS).is_some());
            let mut t = w.row; t[T6_COL_SIGN] = F::ONE - t[T6_COL_SIGN]; assert!(check_row(&DecompressAir, &t, T6_N_CONSTRAINTS).is_some());
        }
        // unreduced y: y = p + 1 encodes the point (0, 1)... (0,1) has x = 0: valid encoding with ge = 1
        let mut a = P_25519; a[0] += 1; // p + 1 (< 2^255)
        let w = make_decompress_row(&a);
        assert_eq!(check_row(&DecompressAir, &w.row, T6_N_CONSTRAINTS), None);
        assert_eq!(w.ycan, { let mut o = [0u8; 32]; o[0] = 1; o }); assert_eq!(w.ax, [0u8; 32]);
    }
    #[test]
    fn signer_scalar_reduces_and_recodes() {
        let mut x = 99u64;
        for _ in 0..5 {
            let mut k = [0i64; 32]; for l in k.iter_mut() { x ^= x << 13; x ^= x >> 7; x ^= x << 17; *l = (x % (1 << 21)) as i64; }
            let (row, kred) = make_signer_scalar_row(&k);
            assert_eq!(check_row(&SignerScalarAir, &row, T7_N_CONSTRAINTS), None);
            let l = modulus_int(&L_25519);
            let kint = { let mut acc = BigInt::zero(); for (i, &v) in k.iter().enumerate() { acc += BigInt::from(v) << (8 * i); } acc };
            assert_eq!(limbs_to_int(&kred), kint.mod_floor(&l));
            let mut acc = BigInt::zero();
            for j in 0..T7_WINDOWS { let m = row[T7_COL_M + j].as_canonical_u32() as i64; let s = row[T7_COL_SGN + j].as_canonical_u32() as i64; acc += BigInt::from((1 - 2 * s) * m) << (10 * j); }
            assert_eq!(acc, limbs_to_int(&kred));
            let mut t = row; t[T7_COL_BITS + 10] = F::ONE - t[T7_COL_BITS + 10]; assert!(check_row(&SignerScalarAir, &t, T7_N_CONSTRAINTS).is_some());
        }
    }
}
