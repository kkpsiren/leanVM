//! T1 `EdSig` (spec §3.1), standalone: one row per signature (kind 0) or per distinct signer (kind 1).
//! Input Q = (x, y) as byte limbs (the prover's torsion witness); the row proves
//!   - Q is on the curve:            y² − x² − 1 − d·x²y² ≡ 0
//!   - P = 8Q by three complete affine doublings  x' = 2xy/(y²−x²),  y' = (y²+x²)/(2 − (y²−x²))
//!     (denominators never vanish on-curve since ±1/d are non-squares); 2x enters as an exact
//!     byte carry chain u = 2x so every identity has weight ≤ 3 (spec §4 / F9)
//!   - P is canonical: (p−1) − P.x ≥ 0 and (p−1) − P.y ≥ 0 by borrow chains
//!   - P ≠ O: with φ boolean, (φ·P.x + (1−φ)·P.y − (1−φ))·inv ≡ 1 (mod p)
//!   - sign bit: P.x[0] = 2h + b  (R bytes := P.y with byte 31 |= 128·b, i.e. `compress`)
//!   - nx = p − P.x by an exact borrow chain (the negated x pushed to T3 for −R terms)
//! Bytes, carries, borrows and the 7-bit h are range-checked by the LogUp sections in the VM
//! integration; here only the arithmetic identities and booleanity are emitted.

use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};

use crate::edadd::{Affine, D_LIMBS, affine_add, is_on_curve};
use crate::gadgets::*;

// ---- layout ---------------------------------------------------------------------------------------
pub const COL_QX: usize = 0;
pub const COL_QY: usize = 32;
/// per doubling k (k = 0,1,2): t1 (130) t2 (130) u (32) uc (32 carries) x (32) y (32) xh (98) yh (98) = 584
pub const DBL_W: usize = 584;
pub const COL_DBL: usize = 64;
pub const COL_F: usize = COL_DBL + 3 * DBL_W;      // 130: f ≡ t1·t2 of doubling 0 (x²·y²)
pub const COL_OC: usize = COL_F + 130;             // 98: on-curve zero-check
pub const COL_CANX: usize = COL_OC + 98;           // 64: diff(32) + borrows(32) for (p−1) − P.x
pub const COL_CANY: usize = COL_CANX + 64;
pub const COL_PHI: usize = COL_CANY + 64;          // 1
pub const COL_INV: usize = COL_PHI + 1;            // 32
pub const COL_NZ: usize = COL_INV + 32;            // 98: nonzero zero-check
pub const COL_H: usize = COL_NZ + 98;              // 1 (7-bit)
pub const COL_B: usize = COL_H + 1;                // 1 sign bit
pub const COL_NX: usize = COL_B + 1;               // 64: nx(32) + borrows(32) for p − P.x
pub const N_COLS: usize = COL_NX + 64;             // 2,313

const fn dbl(k: usize) -> (usize, usize, usize, usize, usize, usize, usize, usize) {
    let b = COL_DBL + k * DBL_W;
    (b, b + 130, b + 260, b + 292, b + 324, b + 356, b + 388, b + 486) // t1 t2 u uc x y xh yh
}

#[derive(Debug, Clone, Copy, Default)]
pub struct EdSigAir;

impl Air for EdSigAir {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 4 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { 0 }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let one = AB::IF::ONE;
        let f = |x: usize| AB::F::from_usize(x);
        let sl = |base: usize, n: usize| -> Vec<AB::IF> { c[base..base + n].to_vec() };
        let d: Vec<AB::IF> = D_LIMBS.iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        let one_limbs: Vec<AB::IF> = (0..32).map(|i| if i == 0 { one.clone() } else { AB::IF::ZERO }).collect();
        let p_limbs: Vec<usize> = P_25519.iter().map(|&b| b as usize).collect();
        let hints = |base: usize| -> HintCols<'_, AB::IF> { HintCols { r: None, q: &c[base..base + QL], w: &c[base + QL..base + QL + WL] } };
        let hints_r = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };

        // 1. doublings
        let (mut x, mut y) = (sl(COL_QX, 32), sl(COL_QY, 32));
        let mut t1_0: Option<Vec<AB::IF>> = None; let mut t2_0: Option<Vec<AB::IF>> = None;
        for k in 0..3 {
            let (bt1, bt2, bu, buc, bx, by, bxh, byh) = dbl(k);
            let (t1, h1) = hints_r(bt1); eval_identity(builder, &one, &[(&x, &x, true)], &[], &h1, &P_25519);
            let (t2, h2) = hints_r(bt2); eval_identity(builder, &one, &[(&y, &y, true)], &[], &h2, &P_25519);
            // u = 2x exact: u_i + 256·c_i = 2·x_i + c_{i−1}, c boolean, c_31 = 0
            let u = sl(bu, 32); let uc = sl(buc, 32);
            for i in 0..32 {
                let prev = if i == 0 { AB::IF::ZERO } else { uc[i - 1].clone() };
                builder.assert_zero(u[i].clone() + uc[i].clone() * f(256) - x[i].clone().double() - prev);
                builder.assert_bool(uc[i].clone());
            }
            builder.assert_zero(uc[31].clone());
            let (nx, ny) = (sl(bx, 32), sl(by, 32));
            // x'·(t2 − t1) ≡ u·y:  x'·t2 − x'·t1 − u·y ≡ 0
            eval_identity(builder, &one, &[(&nx, &t2, true), (&nx, &t1, false), (&u, &y, false)], &[], &hints(bxh), &P_25519);
            // y'·(2 − t2 + t1) ≡ t2 + t1:  2y' − y'·t2 + y'·t1 − t2 − t1 ≡ 0
            eval_identity(builder, &one, &[(&ny, &t2, false), (&ny, &t1, true)], &[(&ny, true), (&ny, true), (&t2, false), (&t1, false)], &hints(byh), &P_25519);
            if k == 0 { t1_0 = Some(t1); t2_0 = Some(t2); }
            x = nx; y = ny;
        }
        // 2. on-curve for Q: f ≡ t1·t2 (= x²y²), then t2 − t1 − 1 − d·f ≡ 0
        let (t1, t2) = (t1_0.unwrap(), t2_0.unwrap());
        let (fv, hf) = hints_r(COL_F); eval_identity(builder, &one, &[(&t1, &t2, true)], &[], &hf, &P_25519);
        eval_identity(builder, &one, &[(&d, &fv, false)], &[(&t2, true), (&t1, false), (&one_limbs, false)], &hints(COL_OC), &P_25519);
        // 3. canonical P = (x, y): (p−1) − P = diff ≥ 0 with boolean borrows, final borrow 0
        let (px, py) = (x.clone(), y.clone());
        for (base, v) in [(COL_CANX, &px), (COL_CANY, &py)] {
            let diff = sl(base, 32); let bw = sl(base + 32, 32);
            for i in 0..32 {
                let pm1 = if i == 0 { p_limbs[0] - 1 } else { p_limbs[i] };
                let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
                // pm1_i − v_i − prev = diff_i − 256·bw_i
                builder.assert_zero(AB::IF::from_usize(pm1) - v[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256));
                builder.assert_bool(bw[i].clone());
            }
            builder.assert_zero(bw[31].clone());
        }
        // 4. P ≠ O: (φ·x + (1−φ)·y − (1−φ))·inv ≡ 1
        let phi = c[COL_PHI].clone(); builder.assert_bool(phi.clone());
        let inv = sl(COL_INV, 32);
        let sel: Vec<AB::IF> = (0..32).map(|i| phi.clone() * px[i].clone() + (one.clone() - phi.clone()) * py[i].clone()).collect();
        let minus: Vec<AB::IF> = (0..32).map(|i| (one.clone() - phi.clone()) * inv[i].clone()).collect();
        eval_identity(builder, &one, &[(&sel, &inv, true)], &[(&minus, false), (&one_limbs, false)], &hints(COL_NZ), &P_25519);
        // 5. sign: x[0] = 2h + b
        let (h, b) = (c[COL_H].clone(), c[COL_B].clone());
        builder.assert_bool(b.clone());
        builder.assert_zero(px[0].clone() - h.double() - b);
        // 6. nx = p − P.x exact borrow chain: p_i − x_i − prev = nx_i − 256·bw_i
        let nx = sl(COL_NX, 32); let bw = sl(COL_NX + 32, 32);
        for i in 0..32 {
            let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(AB::IF::from_usize(p_limbs[i]) - px[i].clone() - prev - nx[i].clone() + bw[i].clone() * f(256));
            builder.assert_bool(bw[i].clone());
        }
        builder.assert_zero(bw[31].clone());
    }
}
// doublings: 3 × (4·65 + 32 + 32 + 1) = 975; on-curve 130; canonical 2×65 = 130; nonzero 65 + 1; sign 2; nx 65
pub const N_CONSTRAINTS: usize = 975 + 130 + 130 + 66 + 2 + 65;

// ---- trace ------------------------------------------------------------------------------------------
pub struct EdSigWitness { pub row: [F; N_COLS], pub p: Affine, pub r_bytes: [u8; 32] }

/// Build the row for torsion witness Q; returns P = 8Q and the compressed R bytes.
pub fn make_row(q: &Affine) -> EdSigWitness {
    assert!(is_on_curve(q));
    let m = &P_25519;
    let fu = |b: u8| F::from_usize(b as usize);
    let mut row = [F::ZERO; N_COLS];
    for i in 0..32 { row[COL_QX + i] = fu(q.x[i]); row[COL_QY + i] = fu(q.y[i]); }
    let put_r = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
    let put_z = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..QL { row[base + i] = fu(w.q[i]); } for i in 0..WL { row[base + QL + i] = F::from_usize(w.w[i] as usize); } };
    let (mut x, mut y) = (q.x, q.y);
    let mut t_first = ([0u8; 32], [0u8; 32]);
    for k in 0..3 {
        let (bt1, bt2, bu, buc, bx, by, bxh, byh) = dbl(k);
        let t1 = mod_mul(&x, &x, m); let t2 = mod_mul(&y, &y, m);
        put_r(&mut row, bt1, &make_identity(&[(&x, &x, true)], &[], false, m));
        put_r(&mut row, bt2, &make_identity(&[(&y, &y, true)], &[], false, m));
        // u = 2x exact with carries
        let mut u = [0u8; 32]; let mut uc = [0u8; 32]; let mut carry = 0u32;
        for i in 0..32 { let s = 2 * x[i] as u32 + carry; u[i] = (s & 255) as u8; carry = s >> 8; uc[i] = carry as u8; }
        assert_eq!(carry, 0, "x must be < 2^255");
        for i in 0..32 { row[bu + i] = fu(u[i]); row[buc + i] = fu(uc[i]); }
        let dbl_pt = affine_add(&Affine { x, y }, &Affine { x, y });
        for i in 0..32 { row[bx + i] = fu(dbl_pt.x[i]); row[by + i] = fu(dbl_pt.y[i]); }
        put_z(&mut row, bxh, &make_identity(&[(&dbl_pt.x, &t2, true), (&dbl_pt.x, &t1, false), (&u, &y, false)], &[], true, m));
        put_z(&mut row, byh, &make_identity(&[(&dbl_pt.y, &t2, false), (&dbl_pt.y, &t1, true)], &[(&dbl_pt.y, true), (&dbl_pt.y, true), (&t2, false), (&t1, false)], true, m));
        if k == 0 { t_first = (t1, t2); }
        x = dbl_pt.x; y = dbl_pt.y;
    }
    let (t1, t2) = t_first;
    let fv = mod_mul(&t1, &t2, m);
    put_r(&mut row, COL_F, &make_identity(&[(&t1, &t2, true)], &[], false, m));
    let one = { let mut o = [0u8; 32]; o[0] = 1; o };
    put_z(&mut row, COL_OC, &make_identity(&[(&D_LIMBS, &fv, false)], &[(&t2, true), (&t1, false), (&one, false)], true, m));
    let p = Affine { x, y };
    // canonical borrow chains: (p−1) − v
    for (base, v) in [(COL_CANX, &p.x), (COL_CANY, &p.y)] {
        let mut borrow = 0i32;
        for i in 0..32 { let pm1 = if i == 0 { P_25519[0] as i32 - 1 } else { P_25519[i] as i32 }; let mut dd = pm1 - v[i] as i32 - borrow; borrow = 0; if dd < 0 { dd += 256; borrow = 1; } row[base + i] = fu(dd as u8); row[base + 32 + i] = fu(borrow as u8); }
        assert_eq!(borrow, 0, "P must be canonical");
    }
    // P ≠ O
    let phi = if p.x != [0u8; 32] { 1u8 } else { 0u8 };
    row[COL_PHI] = fu(phi);
    let target = if phi == 1 { p.x } else { mod_sub(&p.y, &one, m) };
    assert!(target != [0u8; 32], "P is the identity");
    let inv = mod_inv(&target, m);
    for i in 0..32 { row[COL_INV + i] = fu(inv[i]); }
    let sel = if phi == 1 { p.x } else { p.y };
    let minus = if phi == 1 { [0u8; 32] } else { inv };
    put_z(&mut row, COL_NZ, &make_identity(&[(&sel, &inv, true)], &[(&minus, false), (&one, false)], true, m));
    // sign
    row[COL_H] = fu(p.x[0] >> 1); row[COL_B] = fu(p.x[0] & 1);
    // nx = p − x
    { let mut borrow = 0i32; for i in 0..32 { let mut dd = P_25519[i] as i32 - p.x[i] as i32 - borrow; borrow = 0; if dd < 0 { dd += 256; borrow = 1; } row[COL_NX + i] = fu(dd as u8); row[COL_NX + 32 + i] = fu(borrow as u8); } assert_eq!(borrow, 0); }
    let mut r_bytes = p.y; r_bytes[31] |= (p.x[0] & 1) << 7;
    EdSigWitness { row, p, r_bytes }
}

pub fn generate_trace(qs: &[Affine], n_rows: usize) -> (Vec<Vec<F>>, Vec<EdSigWitness>) {
    assert!(qs.len() < n_rows);
    let wits: Vec<EdSigWitness> = qs.iter().map(make_row).collect();
    let mut cols: Vec<Vec<F>> = (0..N_COLS).map(|_| vec![F::ZERO; n_rows]).collect();
    for (r, w) in wits.iter().enumerate() { for c in 0..N_COLS { cols[c][r] = w.row[c]; } }
    // padding rows: a valid row for the base point (never used by any bus)
    let pad = make_row(&crate::edadd::base_point());
    for r in wits.len()..n_rows { for c in 0..N_COLS { cols[c][r] = pad.row[c]; } }
    (cols, wits)
}

pub struct DebugBuilder<'a> { pub flat: &'a [F], pub idx: usize, pub failures: Vec<usize> }
impl<'a> AirBuilder for DebugBuilder<'a> {
    type F = F; type IF = F; type EF = EF;
    fn flat(&self) -> &[F] { self.flat }
    fn shift(&self) -> &[F] { &[] }
    fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.failures.push(self.idx); } self.idx += 1; }
    fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.failures.push(self.idx); } self.idx += 1; }
}
pub fn check_trace(cols: &[Vec<F>]) -> Option<(usize, usize)> {
    let n_rows = cols[0].len(); let extra = ExtraDataForBuses::new(&[], vec![]);
    for r in 0..n_rows {
        let flat: Vec<F> = (0..N_COLS).map(|c| cols[c][r]).collect();
        let mut b = DebugBuilder { flat: &flat, idx: 0, failures: vec![] };
        EdSigAir.eval(&mut b, &extra);
        assert_eq!(b.idx, N_CONSTRAINTS, "N_CONSTRAINTS mismatch: counted {}", b.idx);
        if let Some(&c) = b.failures.first() { return Some((r, c)); }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::edadd::{random_points, scalar_mul_small};
    #[test]
    fn edsig_rows_hold_and_p_is_8q() {
        let qs = random_points(6, 3);
        let (cols, wits) = generate_trace(&qs, 8);
        assert_eq!(check_trace(&cols), None);
        for (q, w) in qs.iter().zip(&wits) { assert_eq!(w.p, scalar_mul_small(q, 8)); assert!(is_on_curve(&w.p)); assert_eq!(w.r_bytes[..31], w.p.y[..31]); }
        // tamper Q.y -> on-curve or doubling identities fail
        let (mut cols, _) = generate_trace(&qs, 8); cols[COL_QY + 2][1] += F::ONE; assert!(check_trace(&cols).is_some());
        // tamper the sign bit
        let (mut cols, _) = generate_trace(&qs, 8); cols[COL_B][0] = F::ONE - cols[COL_B][0]; assert!(check_trace(&cols).is_some());
        // tamper nx
        let (mut cols, _) = generate_trace(&qs, 8); cols[COL_NX + 7][2] += F::ONE; assert!(check_trace(&cols).is_some());
    }
}
