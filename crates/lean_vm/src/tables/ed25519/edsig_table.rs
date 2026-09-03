//! T1 `EdSig` as a VM table: `ed_sig(q_ptr, out_ptr, 0)`.
//!   reads  m[q_ptr .. +64]   = Q = (x, y) byte limbs (the prover's torsion witness)
//!   writes m[out_ptr .. +97] = P.x (32) ‖ P.y (32) ‖ sign bit b (1) ‖ nx = p − P.x (32)
//! and proves Q on-curve, P = 8Q (three complete doublings), P canonical, P ≠ O, b = lsb(P.x).
//! R bytes = P.y with byte 31 += 128·b are assembled by the driver. Every constraint is gated by the
//! multiplicity column so padding rows (all zero, pointers at the zero region) are valid.

use crate::execution::memory::MemoryAccess;
use crate::tables::ed25519::curve::*;
use crate::tables::ed25519::gadgets::*;
use crate::*;
use backend::*;

pub const ED_SIG_NAME: &str = "ed_sig";
pub const LOGUP_EDSIG_DOMAINSEP: usize = 10;

pub const COL_MULT: usize = 0;
pub const COL_NU_A: usize = 1;
pub const COL_NU_B: usize = 2;
pub const COL_NU_C: usize = 3;
pub const COL_Q: usize = 4;              // 64: QX (32) QY (32)
pub const COL_OUT: usize = 68;           // 97: PX (32) PY (32) B (1) NX (32)
pub const COL_PX: usize = 68;
pub const COL_PY: usize = 100;
pub const COL_B: usize = 132;
pub const COL_NX: usize = 133;
pub const N_OUT: usize = 97;
pub const COL_DBL: usize = 165;          // dbl0 (584), dbl1 (584), dbl2 (520: x,y are OUT)
pub const DBL_W: usize = 584;
pub const COL_F: usize = COL_DBL + 2 * DBL_W + 520;   // 130
pub const COL_OC: usize = COL_F + 130;                // 98
pub const COL_CANX: usize = COL_OC + 98;              // 64
pub const COL_CANY: usize = COL_CANX + 64;            // 64
pub const COL_PHI: usize = COL_CANY + 64;             // 1
pub const COL_INV: usize = COL_PHI + 1;               // 32
pub const COL_NZ: usize = COL_INV + 32;               // 98
pub const COL_H: usize = COL_NZ + 98;                 // 1
pub const COL_NXB: usize = COL_H + 1;                 // 32 borrows of nx
pub const N_COLS: usize = COL_NXB + 32;               // 2,373

/// (t1, t2, u, uc, x, y, xh, yh) column bases of doubling k; for k = 2 the outputs are the OUT block.
const fn dbl(k: usize) -> (usize, usize, usize, usize, usize, usize, usize, usize) {
    let b = COL_DBL + k * DBL_W;
    if k < 2 { (b, b + 130, b + 260, b + 292, b + 324, b + 356, b + 388, b + 486) }
    else { (b, b + 130, b + 260, b + 292, COL_PX, COL_PY, b + 324, b + 422) }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdSigTable<const BUS: bool>;

impl<const BUS: bool> Air for EdSigTable<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 4 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { 0 }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let one = AB::IF::ONE;
        let f = |x: usize| AB::F::from_usize(x);
        let mult = c[COL_MULT].clone();
        let (nu_a, nu_b, nu_c) = (c[COL_NU_A].clone(), c[COL_NU_B].clone(), c[COL_NU_C].clone());
        let ds = AB::IF::from_usize(LOGUP_EDSIG_DOMAINSEP);
        if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, mult.clone(), ds, &[nu_a, nu_b, nu_c.clone()]); }
        else { builder.declare_values(&[mult.clone()]); builder.declare_values(&[nu_a, nu_b, nu_c.clone(), ds]); }
        builder.assert_bool(mult.clone());
        builder.assert_zero(nu_c);
        let g = mult.clone();
        let sl = |base: usize, n: usize| -> Vec<AB::IF> { c[base..base + n].to_vec() };
        let d: Vec<AB::IF> = D_LIMBS.iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        let one_limbs: Vec<AB::IF> = (0..32).map(|i| if i == 0 { one.clone() } else { AB::IF::ZERO }).collect();
        let p_limbs: Vec<usize> = P_25519.iter().map(|&b| b as usize).collect();
        let hints = |base: usize| -> HintCols<'_, AB::IF> { HintCols { r: None, q: &c[base..base + QL], w: &c[base + QL..base + QL + WL] } };
        let hints_r = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };

        let (mut x, mut y) = (sl(COL_Q, 32), sl(COL_Q + 32, 32));
        let mut first: Option<(Vec<AB::IF>, Vec<AB::IF>)> = None;
        for k in 0..3 {
            let (bt1, bt2, bu, buc, bx, by, bxh, byh) = dbl(k);
            let (t1, h1) = hints_r(bt1); eval_identity(builder, &g, &[(&x, &x, true)], &[], &h1, &P_25519);
            let (t2, h2) = hints_r(bt2); eval_identity(builder, &g, &[(&y, &y, true)], &[], &h2, &P_25519);
            let u = sl(bu, 32); let uc = sl(buc, 32);
            for i in 0..32 {
                let prev = if i == 0 { AB::IF::ZERO } else { uc[i - 1].clone() };
                builder.assert_zero(g.clone() * (u[i].clone() + uc[i].clone() * f(256) - x[i].clone().double() - prev));
                builder.assert_bool(uc[i].clone());
            }
            builder.assert_zero(uc[31].clone());
            let (nx, ny) = (sl(bx, 32), sl(by, 32));
            eval_identity(builder, &g, &[(&nx, &t2, true), (&nx, &t1, false), (&u, &y, false)], &[], &hints(bxh), &P_25519);
            eval_identity(builder, &g, &[(&ny, &t2, false), (&ny, &t1, true)], &[(&ny, true), (&ny, true), (&t2, false), (&t1, false)], &hints(byh), &P_25519);
            if k == 0 { first = Some((t1, t2)); }
            x = nx; y = ny;
        }
        let (t1, t2) = first.unwrap();
        let (fv, hf) = hints_r(COL_F); eval_identity(builder, &g, &[(&t1, &t2, true)], &[], &hf, &P_25519);
        eval_identity(builder, &g, &[(&d, &fv, false)], &[(&t2, true), (&t1, false), (&one_limbs, false)], &hints(COL_OC), &P_25519);
        let (px, py) = (x.clone(), y.clone());
        for (base, v) in [(COL_CANX, &px), (COL_CANY, &py)] {
            let diff = sl(base, 32); let bw = sl(base + 32, 32);
            for i in 0..32 {
                let pm1 = if i == 0 { p_limbs[0] - 1 } else { p_limbs[i] };
                let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
                builder.assert_zero(g.clone() * (AB::IF::from_usize(pm1) - v[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256)));
                builder.assert_bool(bw[i].clone());
            }
            builder.assert_zero(bw[31].clone());
        }
        let phi = c[COL_PHI].clone(); builder.assert_bool(phi.clone());
        let inv = sl(COL_INV, 32);
        let sel: Vec<AB::IF> = (0..32).map(|i| phi.clone() * px[i].clone() + (one.clone() - phi.clone()) * py[i].clone()).collect();
        let minus: Vec<AB::IF> = (0..32).map(|i| (one.clone() - phi.clone()) * inv[i].clone()).collect();
        eval_identity(builder, &g, &[(&sel, &inv, true)], &[(&minus, false), (&one_limbs, false)], &hints(COL_NZ), &P_25519);
        let (h, b) = (c[COL_H].clone(), c[COL_B].clone());
        builder.assert_bool(b.clone());
        builder.assert_zero(g.clone() * (px[0].clone() - h.double() - b));
        let nx = sl(COL_NX, 32); let bw = sl(COL_NXB, 32);
        for i in 0..32 {
            let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(g.clone() * (AB::IF::from_usize(p_limbs[i]) - px[i].clone() - prev - nx[i].clone() + bw[i].clone() * f(256)));
            builder.assert_bool(bw[i].clone());
        }
        builder.assert_zero(bw[31].clone());
    }
}
pub const N_CONSTRAINTS: usize = 2 + 2 + 975 + 130 + 130 + 66 + 2 + 65;

impl<const BUS: bool> TableT for EdSigTable<BUS> {
    fn name(&self) -> &'static str { "ed_sig" }
    fn table(&self) -> Table { Table::ed_sig() }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(COL_MULT),
            domainsep: BusData::Constant(LOGUP_EDSIG_DOMAINSEP),
            data: vec![BusData::Column(COL_NU_A), BusData::Column(COL_NU_B), BusData::Column(COL_NU_C)],
        }];
        buses.extend(memory_lookups_consecutive(COL_NU_A, COL_Q, 64));
        buses.extend(memory_lookups_consecutive(COL_NU_B, COL_OUT, N_OUT));
        let (u8s, u16s, u7s) = range_cols();
        buses.extend(range_lookups(&u8s, RANGE_U8));
        buses.extend(range_lookups(&u16s, RANGE_U16));
        buses.extend(range_lookups(&u7s, RANGE_U7));
        buses
    }
    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; N_COLS];
        row[COL_NU_A] = F::from_usize(zero_vec_ptr); row[COL_NU_B] = F::from_usize(zero_vec_ptr);
        row
    }
    #[inline(always)]
    fn execute<M: MemoryAccess>(&self, arg_a: F, arg_b: F, arg_c: F, _args: PrecompileCompTimeArgs<usize>, ctx: &mut InstructionContext<'_, M>) -> Result<(), RunnerError> {
        let q_ptr = arg_a.to_usize(); let out_ptr = arg_b.to_usize();
        let mut cells = [F::ZERO; 64];
        ctx.memory.get_slice_into(q_ptr, &mut cells)?;
        let byte = |x: F| -> u8 { let v = x.as_canonical_u32(); assert!(v < 256, "ed_sig: Q limb is not a byte"); v as u8 };
        let q = Affine { x: std::array::from_fn(|i| byte(cells[i])), y: std::array::from_fn(|i| byte(cells[32 + i])) };
        let row = make_row(&q, q_ptr, out_ptr);
        ctx.memory.set_slice(out_ptr, &row[COL_OUT..COL_OUT + N_OUT])?;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        for (i, v) in row.iter().enumerate() { trace.columns[i].push(*v); }
        let _ = arg_c;
        Ok(())
    }
}

/// Every limb column by range class: (bytes, u16 witness limbs, 7-bit).
pub fn range_cols() -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let (mut u8s, mut u16s) = (vec![], vec![]);
    fn rng(v: &mut Vec<usize>, b: usize, n: usize) { v.extend(b..b + n) }
    fn with_r(u8s: &mut Vec<usize>, u16s: &mut Vec<usize>, b: usize) { rng(u8s, b, 32 + QL); rng(u16s, b + 66, WL); }
    fn zero(u8s: &mut Vec<usize>, u16s: &mut Vec<usize>, b: usize) { rng(u8s, b, QL); rng(u16s, b + QL, WL); }
    rng(&mut u8s, COL_Q, 64); rng(&mut u8s, COL_PX, 64); rng(&mut u8s, COL_NX, 32);
    for k in 0..3 {
        let (bt1, bt2, bu, _buc, bx, by, bxh, byh) = dbl(k);
        with_r(&mut u8s, &mut u16s, bt1); with_r(&mut u8s, &mut u16s, bt2); rng(&mut u8s, bu, 32);
        if k < 2 { rng(&mut u8s, bx, 32); rng(&mut u8s, by, 32); }
        zero(&mut u8s, &mut u16s, bxh); zero(&mut u8s, &mut u16s, byh);
    }
    with_r(&mut u8s, &mut u16s, COL_F); zero(&mut u8s, &mut u16s, COL_OC);
    rng(&mut u8s, COL_CANX, 32); rng(&mut u8s, COL_CANY, 32); rng(&mut u8s, COL_INV, 32); zero(&mut u8s, &mut u16s, COL_NZ);
    (u8s, u16s, vec![COL_H])
}

/// The full row for torsion witness Q (mult = 1, pointers as given).
pub fn make_row(q: &Affine, q_ptr: usize, out_ptr: usize) -> [F; N_COLS] {
    assert!(is_on_curve(q), "ed_sig: Q is not on the curve");
    let m = &P_25519;
    let fu = |b: u8| F::from_usize(b as usize);
    let mut row = [F::ZERO; N_COLS];
    row[COL_MULT] = F::ONE; row[COL_NU_A] = F::from_usize(q_ptr); row[COL_NU_B] = F::from_usize(out_ptr);
    for i in 0..32 { row[COL_Q + i] = fu(q.x[i]); row[COL_Q + 32 + i] = fu(q.y[i]); }
    let put_r = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
    let put_z = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..QL { row[base + i] = fu(w.q[i]); } for i in 0..WL { row[base + QL + i] = F::from_usize(w.w[i] as usize); } };
    let (mut x, mut y) = (q.x, q.y);
    let mut first = ([0u8; 32], [0u8; 32]);
    for k in 0..3 {
        let (bt1, bt2, bu, buc, bx, by, bxh, byh) = dbl(k);
        let t1 = mod_mul(&x, &x, m); let t2 = mod_mul(&y, &y, m);
        put_r(&mut row, bt1, &make_identity(&[(&x, &x, true)], &[], false, m));
        put_r(&mut row, bt2, &make_identity(&[(&y, &y, true)], &[], false, m));
        let mut u = [0u8; 32]; let mut uc = [0u8; 32]; let mut carry = 0u32;
        for i in 0..32 { let s = 2 * x[i] as u32 + carry; u[i] = (s & 255) as u8; carry = s >> 8; uc[i] = carry as u8; }
        assert_eq!(carry, 0, "x must be < 2^255");
        for i in 0..32 { row[bu + i] = fu(u[i]); row[buc + i] = fu(uc[i]); }
        let dp = affine_add(&Affine { x, y }, &Affine { x, y });
        for i in 0..32 { row[bx + i] = fu(dp.x[i]); row[by + i] = fu(dp.y[i]); }
        put_z(&mut row, bxh, &make_identity(&[(&dp.x, &t2, true), (&dp.x, &t1, false), (&u, &y, false)], &[], true, m));
        put_z(&mut row, byh, &make_identity(&[(&dp.y, &t2, false), (&dp.y, &t1, true)], &[(&dp.y, true), (&dp.y, true), (&t2, false), (&t1, false)], true, m));
        if k == 0 { first = (t1, t2); }
        x = dp.x; y = dp.y;
    }
    let (t1, t2) = first;
    let fv = mod_mul(&t1, &t2, m);
    put_r(&mut row, COL_F, &make_identity(&[(&t1, &t2, true)], &[], false, m));
    let one = { let mut o = [0u8; 32]; o[0] = 1; o };
    put_z(&mut row, COL_OC, &make_identity(&[(&D_LIMBS, &fv, false)], &[(&t2, true), (&t1, false), (&one, false)], true, m));
    let p = Affine { x, y };
    for (base, v) in [(COL_CANX, &p.x), (COL_CANY, &p.y)] {
        let mut borrow = 0i32;
        for i in 0..32 { let pm1 = if i == 0 { P_25519[0] as i32 - 1 } else { P_25519[i] as i32 }; let mut dd = pm1 - v[i] as i32 - borrow; borrow = 0; if dd < 0 { dd += 256; borrow = 1; } row[base + i] = fu(dd as u8); row[base + 32 + i] = fu(borrow as u8); }
        assert_eq!(borrow, 0, "P must be canonical");
    }
    let phi = if p.x != [0u8; 32] { 1u8 } else { 0u8 };
    row[COL_PHI] = fu(phi);
    let target = if phi == 1 { p.x } else { mod_sub(&p.y, &one, m) };
    assert!(target != [0u8; 32], "P is the identity");
    let inv = mod_inv(&target, m);
    for i in 0..32 { row[COL_INV + i] = fu(inv[i]); }
    let sel = if phi == 1 { p.x } else { p.y };
    let minus = if phi == 1 { [0u8; 32] } else { inv };
    put_z(&mut row, COL_NZ, &make_identity(&[(&sel, &inv, true)], &[(&minus, false), (&one, false)], true, m));
    row[COL_H] = fu(p.x[0] >> 1); row[COL_B] = fu(p.x[0] & 1);
    { let mut borrow = 0i32; for i in 0..32 { let mut dd = P_25519[i] as i32 - p.x[i] as i32 - borrow; borrow = 0; if dd < 0 { dd += 256; borrow = 1; } row[COL_NX + i] = fu(dd as u8); row[COL_NXB + i] = fu(borrow as u8); } assert_eq!(borrow, 0); }
    row
}

/// R bytes as the driver assembles them: P.y with byte 31 |= 128·b.
pub fn r_bytes_of(row: &[F]) -> [u8; 32] { let mut r = [0u8; 32]; for i in 0..32 { r[i] = row[COL_PY + i].as_canonical_u32() as u8; } r[31] |= (row[COL_B].as_canonical_u32() as u8) << 7; r }
