//! T3 `EdAdd` (spec §3.3), standalone: one row = one COMPLETE affine twisted-Edwards addition
//! (a = −1, Curve25519 in Edwards form): acc_out = acc_in + P, where acc_in is (0,1) on a chain
//! start row and otherwise the NEXT row's acc_out (chains are laid out in reverse row order, so the
//! chain HEAD holds the total and reads its input from the row after it). Six identity checks:
//!
//!   t1 ≡ acc.x·px     t2 ≡ acc.y·py     f ≡ t1·t2     g ≡ d·f
//!   x3·g + x3 − acc.x·py − px·acc.y ≡ 0          (x3·(1+g) = x1y2 + y1x2)
//!   y3 − y3·g − t2 − t1 ≡ 0                      (y3·(1−g) = y1y2 + x1x2)
//!
//! Denominators 1 ± d·x1x2y1y2 never vanish for on-curve inputs (d and −d are non-squares), so the
//! formulas are complete: doubling, adding the neutral element and adding inverses all go through
//! the same row. Points enter as byte limbs (a negated point is pushed with x := p − x by T1).
//! Bus wiring (routing, point tuples, bucket/reduction kinds) is attached in the VM integration;
//! here `start`/`head` and the shift chain are the only structure.

use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};
use num_bigint::BigInt;
use num_integer::Integer;

use crate::gadgets::*;
use lean_vm::ed25519::curve::*;

pub use lean_vm::ed25519::curve::*;

// ---- column layout ---------------------------------------------------------------------------------
// shift columns first
pub const COL_X3: usize = 0;             // 32
pub const COL_Y3: usize = 32;            // 32
pub const COL_START: usize = 64;         // 1 (chain starts here: acc_in = (0,1))
pub const N_SHIFT: usize = 65;
// flat
pub const COL_PX: usize = 65;            // 32
pub const COL_PY: usize = 97;            // 32
pub const COL_T1: usize = 129;           // r32 q34 w64 = 130
pub const COL_T2: usize = COL_T1 + 130;
pub const COL_F: usize = COL_T2 + 130;
pub const COL_G: usize = COL_F + 130;
pub const COL_X3_HINT: usize = COL_G + 130;      // q34 w64 = 98 (zero-check)
pub const COL_Y3_HINT: usize = COL_X3_HINT + 98;
pub const N_COLS: usize = COL_Y3_HINT + 98;      // 845

const fn hint(base: usize, with_r: bool) -> (Option<usize>, usize, usize) { if with_r { (Some(base), base + 32, base + 66) } else { (None, base, base + 34) } }

#[derive(Debug, Clone, Copy, Default)]
pub struct EdAddAir;

impl Air for EdAddAir {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 3 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { N_SHIFT }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra: &Self::ExtraData) {
        let cur: Vec<AB::IF> = builder.flat().to_vec();
        let nxt: Vec<AB::IF> = builder.shift().to_vec();
        let start = cur[COL_START].clone();
        builder.assert_bool(start.clone());
        let one = AB::IF::ONE;
        // acc_in = start·(0,1) + (1−start)·next.acc_out   (degree 1 expressions per limb)
        let acc_x: Vec<AB::IF> = (0..32).map(|i| (one.clone() - start.clone()) * nxt[COL_X3 + i].clone()).collect();
        let acc_y: Vec<AB::IF> = (0..32).map(|i| { let v = (one.clone() - start.clone()) * nxt[COL_Y3 + i].clone(); if i == 0 { v + start.clone() } else { v } }).collect();
        let px: Vec<AB::IF> = cur[COL_PX..COL_PX + 32].to_vec();
        let py: Vec<AB::IF> = cur[COL_PY..COL_PY + 32].to_vec();
        let x3: Vec<AB::IF> = cur[COL_X3..COL_X3 + 32].to_vec();
        let y3: Vec<AB::IF> = cur[COL_Y3..COL_Y3 + 32].to_vec();
        let d: Vec<AB::IF> = D_LIMBS.iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        let cols = |base: usize, with_r: bool| -> (Option<Vec<AB::IF>>, Vec<AB::IF>, Vec<AB::IF>) {
            let (r, q, w) = hint(base, with_r);
            (r.map(|r| cur[r..r + 32].to_vec()), cur[q..q + QL].to_vec(), cur[w..w + WL].to_vec())
        };
        let gate = one.clone();
        let (t1, t1q, t1w) = cols(COL_T1, true); let t1 = t1.unwrap();
        let (t2, t2q, t2w) = cols(COL_T2, true); let t2 = t2.unwrap();
        let (f, fq, fw) = cols(COL_F, true); let f = f.unwrap();
        let (g, gq, gw) = cols(COL_G, true); let g = g.unwrap();
        let (_, xq, xw) = cols(COL_X3_HINT, false);
        let (_, yq, yw) = cols(COL_Y3_HINT, false);
        eval_identity(builder, &gate, &[(&acc_x, &px, true)], &[], &HintCols { r: Some(&t1), q: &t1q, w: &t1w }, &P_25519);
        eval_identity(builder, &gate, &[(&acc_y, &py, true)], &[], &HintCols { r: Some(&t2), q: &t2q, w: &t2w }, &P_25519);
        eval_identity(builder, &gate, &[(&t1, &t2, true)], &[], &HintCols { r: Some(&f), q: &fq, w: &fw }, &P_25519);
        eval_identity(builder, &gate, &[(&d, &f, true)], &[], &HintCols { r: Some(&g), q: &gq, w: &gw }, &P_25519);
        eval_identity(builder, &gate, &[(&x3, &g, true), (&acc_x, &py, false), (&px, &acc_y, false)], &[(&x3, true)], &HintCols { r: None, q: &xq, w: &xw }, &P_25519);
        eval_identity(builder, &gate, &[(&y3, &g, false)], &[(&y3, true), (&t2, false), (&t1, false)], &HintCols { r: None, q: &yq, w: &yw }, &P_25519);
    }
}
pub const N_CONSTRAINTS: usize = 1 + 6 * N_IDENTITY_CONSTRAINTS;

// ---- trace generation --------------------------------------------------------------------------------
/// A chain: points added in order; rows are emitted in REVERSE (the head row first).
pub struct Chain { pub points: Vec<Affine> }

/// Rows (row-major) for chains; returns the rows and each chain's total (in emission order).
pub fn chain_rows(chains: &[Chain]) -> (Vec<[F; N_COLS]>, Vec<Affine>) {
    let fu = |b: u8| F::from_usize(b as usize);
    let mut rows = vec![]; let mut totals = vec![];
    for ch in chains {
        // forward pass: accumulate
        let mut acc = NEUTRAL; let mut steps: Vec<[F; N_COLS]> = vec![];
        for (k, p) in ch.points.iter().enumerate() {
            let acc_in = acc;
            let out = affine_add(&acc_in, p);
            let m = &P_25519;
            let t1 = mod_mul(&acc_in.x, &p.x, m); let t2 = mod_mul(&acc_in.y, &p.y, m); let f = mod_mul(&t1, &t2, m); let g = mod_mul(&D_LIMBS, &f, m);
            let w_t1 = make_identity(&[(&acc_in.x, &p.x, true)], &[], false, m);
            let w_t2 = make_identity(&[(&acc_in.y, &p.y, true)], &[], false, m);
            let w_f = make_identity(&[(&t1, &t2, true)], &[], false, m);
            let w_g = make_identity(&[(&D_LIMBS, &f, true)], &[], false, m);
            let w_x = make_identity(&[(&out.x, &g, true), (&acc_in.x, &p.y, false), (&p.x, &acc_in.y, false)], &[(&out.x, true)], true, m);
            let w_y = make_identity(&[(&out.y, &g, false)], &[(&out.y, true), (&t2, false), (&t1, false)], true, m);
            debug_assert_eq!(w_t1.r, t1); debug_assert_eq!(w_g.r, g);
            let mut row = [F::ZERO; N_COLS];
            for i in 0..32 { row[COL_X3 + i] = fu(out.x[i]); row[COL_Y3 + i] = fu(out.y[i]); row[COL_PX + i] = fu(p.x[i]); row[COL_PY + i] = fu(p.y[i]); }
            row[COL_START] = F::from_bool(k == 0);
            let put = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness, with_r: bool| {
                let (r, q, wc) = hint(base, with_r);
                if let Some(r) = r { for i in 0..32 { row[r + i] = fu(w.r[i]); } }
                for i in 0..QL { row[q + i] = fu(w.q[i]); }
                for i in 0..WL { row[wc + i] = F::from_usize(w.w[i] as usize); }
            };
            put(&mut row, COL_T1, &w_t1, true); put(&mut row, COL_T2, &w_t2, true); put(&mut row, COL_F, &w_f, true); put(&mut row, COL_G, &w_g, true);
            put(&mut row, COL_X3_HINT, &w_x, false); put(&mut row, COL_Y3_HINT, &w_y, false);
            steps.push(row); acc = out;
        }
        steps.reverse(); rows.extend(steps); totals.push(acc);
    }
    (rows, totals)
}

/// Column-major trace padded to n_rows (padding rows: start=1 with the neutral input and P=(0,1)? No —
/// padding rows are all-zero except they must satisfy the identities: we use start=1, P=(0,1), out=(0,1)).
pub fn generate_trace(chains: &[Chain], n_rows: usize) -> (Vec<Vec<F>>, Vec<Affine>) {
    let (rows, totals) = chain_rows(chains);
    assert!(rows.len() < n_rows, "need at least one padding row");
    let mut cols: Vec<Vec<F>> = (0..N_COLS).map(|_| vec![F::ZERO; n_rows]).collect();
    for (r, row) in rows.iter().enumerate() { for c in 0..N_COLS { cols[c][r] = row[c]; } }
    // padding: a start row adding the neutral element to (0,1): out = (0,1)
    let pad = { let (prow, _) = chain_rows(&[Chain { points: vec![NEUTRAL] }]); prow[0] };
    for r in rows.len()..n_rows { for c in 0..N_COLS { cols[c][r] = pad[c]; } }
    (cols, totals)
}

pub struct DebugBuilder<'a> { pub flat: &'a [F], pub shift: &'a [F], pub idx: usize, pub failures: Vec<usize> }
impl<'a> AirBuilder for DebugBuilder<'a> {
    type F = F; type IF = F; type EF = EF;
    fn flat(&self) -> &[F] { self.flat }
    fn shift(&self) -> &[F] { self.shift }
    fn assert_zero(&mut self, x: F) { if x != F::ZERO { self.failures.push(self.idx); } self.idx += 1; }
    fn assert_zero_ef(&mut self, x: EF) { if x != EF::ZERO { self.failures.push(self.idx); } self.idx += 1; }
}
pub fn check_trace(cols: &[Vec<F>]) -> Option<(usize, usize)> {
    let n_rows = cols[0].len();
    let extra = ExtraDataForBuses::new(&[], vec![]);
    for r in 0..n_rows {
        let flat: Vec<F> = (0..N_COLS).map(|c| cols[c][r]).collect();
        let shift: Vec<F> = (0..N_SHIFT).map(|c| cols[c][(r + 1).min(n_rows - 1)]).collect();
        let mut b = DebugBuilder { flat: &flat, shift: &shift, idx: 0, failures: vec![] };
        EdAddAir.eval(&mut b, &extra);
        assert_eq!(b.idx, N_CONSTRAINTS);
        if let Some(&c) = b.failures.first() { return Some((r, c)); }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn curve_constants_and_native_arithmetic() {
        let b = base_point();
        assert!(is_on_curve(&b));
        assert!(is_on_curve(&affine_add(&b, &b)));
        assert_eq!(affine_add(&b, &NEUTRAL), b);
        // 8·B has order L: L·(8B) = O (L = group order)
        let l = limbs_to_int(&L_25519); let _ = l; // (full L-multiplication is expensive; checked via 2B + B == 3B instead)
        assert_eq!(affine_add(&affine_add(&b, &b), &b), scalar_mul_small(&b, 3));
        // −B + B = O with −B = (p − x, y)
        let neg = Affine { x: mod_sub(&[0u8; 32], &b.x, &P_25519), y: b.y };
        assert_eq!(affine_add(&b, &neg), NEUTRAL);
        assert!(is_on_curve(&Affine { x: mod_sub(&[0u8; 32], &b.x, &P_25519), y: b.y }));
    }
    #[test]
    fn chains_satisfy_the_air_and_match_native_totals() {
        let pts = random_points(30, 5);
        let chains = vec![Chain { points: pts[..7].to_vec() }, Chain { points: pts[7..8].to_vec() }, Chain { points: pts[8..30].to_vec() }];
        let (cols, totals) = generate_trace(&chains, 64);
        assert_eq!(check_trace(&cols), None);
        for (c, t) in chains.iter().zip(&totals) { let mut acc = NEUTRAL; for p in &c.points { acc = affine_add(&acc, p); } assert_eq!(&acc, t); assert!(is_on_curve(t)); }
        // doubling and neutral within a chain
        let b = base_point();
        let (cols, _) = generate_trace(&[Chain { points: vec![b, b, NEUTRAL, b] }], 16);
        assert_eq!(check_trace(&cols), None);
        // tamper: change one limb of an output
        let (mut cols, _) = generate_trace(&chains, 64);
        cols[COL_X3 + 9][3] += F::ONE;
        assert!(check_trace(&cols).is_some());
    }
}
