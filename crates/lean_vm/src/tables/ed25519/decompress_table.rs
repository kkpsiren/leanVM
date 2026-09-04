//! T6 `DecompressA` as a VM table: `ed_decompress(a_ptr, out_ptr, 0)`.
//!   reads  m[a_ptr .. +32]   = A (compressed key bytes)
//!   writes m[out_ptr .. +64] = A.x (32) ‖ y_can (32)
//! Mirrors curve25519-dalek decompress incl. the unreduced y (y = A & ~(1<<255) may be ≥ p).
//! Gated by the multiplicity column so padding rows are valid.

use crate::execution::memory::MemoryAccess;
use crate::tables::ed25519::curve::*;
use crate::tables::ed25519::gadgets::*;
use crate::*;
use backend::*;
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::Zero;

pub const ED_DECOMPRESS_NAME: &str = "ed_decompress";
pub const LOGUP_EDDECOMPRESS_DOMAINSEP: usize = 14;

pub const COL_MULT: usize = 0;
pub const COL_NU_A: usize = 1;
pub const COL_NU_B: usize = 2;
pub const COL_NU_C: usize = 3;
pub const COL_A: usize = 4;              // 32
pub const COL_OUT: usize = 36;           // 97: AX (32) YCAN (32) PAD (1) NX (32) — the same shape as EdSig's OUT
pub const COL_AX: usize = 36;
pub const COL_YCAN: usize = 68;
pub const COL_PAD: usize = 100;
pub const COL_NX: usize = 101;
pub const N_OUT: usize = 97;
pub const COL_H: usize = 133;            // 1
pub const COL_SIGN: usize = 134;         // 1
pub const COL_T: usize = 135;            // 130
pub const COL_V: usize = 265;            // 130
pub const COL_XCAN: usize = 395;         // 32
pub const COL_W: usize = 427;            // 130
pub const COL_OC: usize = 557;           // 98
pub const COL_XLT: usize = 655;          // 64
pub const COL_HX: usize = 719;           // 1
pub const COL_NEG: usize = 720;          // 32 borrows of p − x_can
pub const COL_PMX: usize = 752;          // 32: p − x_can
pub const COL_GE: usize = 784;           // 1
pub const COL_YB: usize = 785;           // 32
pub const COL_YLT: usize = 817;          // 64
pub const N_COLS: usize = 881;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdDecompressTable<const BUS: bool>;

impl<const BUS: bool> Air for EdDecompressTable<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 3 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { 0 }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let one = AB::IF::ONE; let f = |x: usize| AB::F::from_usize(x);
        let mult = c[COL_MULT].clone();
        let (nu_a, nu_b, nu_c) = (c[COL_NU_A].clone(), c[COL_NU_B].clone(), c[COL_NU_C].clone());
        let ds = AB::IF::from_usize(LOGUP_EDDECOMPRESS_DOMAINSEP);
        if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, mult.clone(), ds, &[nu_a, nu_b, nu_c.clone()]); }
        else { builder.declare_values(&[mult.clone()]); builder.declare_values(&[nu_a, nu_b, nu_c.clone(), ds]); }
        builder.assert_bool(mult.clone()); builder.assert_zero(nu_c);
        let g = mult.clone();
        let sl = |b: usize, n: usize| -> Vec<AB::IF> { c[b..b + n].to_vec() };
        let hints = |base: usize| -> HintCols<'_, AB::IF> { HintCols { r: None, q: &c[base..base + QL], w: &c[base + QL..base + QL + WL] } };
        let hints_r = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };
        let d: Vec<AB::IF> = D_LIMBS.iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        let one_limbs: Vec<AB::IF> = (0..32).map(|i| if i == 0 { one.clone() } else { AB::IF::ZERO }).collect();
        let p_limbs: Vec<usize> = P_25519.iter().map(|&b| b as usize).collect();
        let a = sl(COL_A, 32);
        let (h, sign) = (c[COL_H].clone(), c[COL_SIGN].clone());
        builder.assert_bool(sign.clone());
        builder.assert_zero(g.clone() * (a[31].clone() - h.clone() - sign.clone() * f(128)));
        let y: Vec<AB::IF> = (0..32).map(|i| if i < 31 { a[i].clone() } else { h.clone() }).collect();
        let (t, ht) = hints_r(COL_T); eval_identity(builder, &g, &[(&y, &y, true)], &[], &ht, &P_25519);
        let (v, hv) = hints_r(COL_V); eval_identity(builder, &g, &[(&d, &t, true)], &[], &hv, &P_25519);
        let xcan = sl(COL_XCAN, 32);
        let (w, hw) = hints_r(COL_W); eval_identity(builder, &g, &[(&xcan, &xcan, true)], &[], &hw, &P_25519);
        eval_identity(builder, &g, &[(&w, &v, true)], &[(&w, true), (&t, false), (&one_limbs, true)], &hints(COL_OC), &P_25519);
        { let diff = sl(COL_XLT, 32); let bw = sl(COL_XLT + 32, 32);
          for i in 0..32 { let pm1 = if i == 0 { p_limbs[0] - 1 } else { p_limbs[i] }; let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(g.clone() * (AB::IF::from_usize(pm1) - xcan[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256))); builder.assert_bool(bw[i].clone()); }
          builder.assert_zero(bw[31].clone()); }
        builder.assert_zero(g.clone() * (xcan[0].clone() - c[COL_HX].clone().double()));
        // pmx = p − x_can (exact borrow chain, always); A.x = sign ? pmx : x_can; nx = p − A.x = sign ? x_can : pmx
        let ax = sl(COL_AX, 32); let nx = sl(COL_NX, 32); let pmx = sl(COL_PMX, 32); let nb = sl(COL_NEG, 32);
        for i in 0..32 {
            let prev = if i == 0 { AB::IF::ZERO } else { nb[i - 1].clone() };
            builder.assert_zero(g.clone() * (AB::IF::from_usize(p_limbs[i]) - xcan[i].clone() - prev - pmx[i].clone() + nb[i].clone() * f(256)));
            builder.assert_bool(nb[i].clone());
            builder.assert_zero(ax[i].clone() - sign.clone() * pmx[i].clone() - (one.clone() - sign.clone()) * xcan[i].clone());
            builder.assert_zero(nx[i].clone() - sign.clone() * xcan[i].clone() - (one.clone() - sign.clone()) * pmx[i].clone());
        }
        builder.assert_zero(nb[31].clone());
        builder.assert_zero(c[COL_PAD].clone());
        let ge = c[COL_GE].clone(); builder.assert_bool(ge.clone());
        let ycan = sl(COL_YCAN, 32); let yb = sl(COL_YB, 32);
        for i in 0..32 {
            let prev = if i == 0 { AB::IF::ZERO } else { yb[i - 1].clone() };
            builder.assert_zero(ge.clone() * (y[i].clone() - AB::IF::from_usize(p_limbs[i]) - prev - ycan[i].clone() + yb[i].clone() * f(256)));
            builder.assert_zero((one.clone() - ge.clone()) * (ycan[i].clone() - y[i].clone()));
            builder.assert_bool(yb[i].clone());
        }
        builder.assert_zero(ge.clone() * yb[31].clone());
        { let diff = sl(COL_YLT, 32); let bw = sl(COL_YLT + 32, 32);
          for i in 0..32 { let pm1 = if i == 0 { p_limbs[0] - 1 } else { p_limbs[i] }; let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(g.clone() * (one.clone() - ge.clone()) * (AB::IF::from_usize(pm1) - y[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256))); builder.assert_bool(bw[i].clone()); }
          builder.assert_zero((one.clone() - ge.clone()) * bw[31].clone()); }
    }
}
pub const N_CONSTRAINTS: usize = 2 + 2 + 2 + 4 * 65 + 65 + 1 + 130 + 1 + 97 + 65;

impl<const BUS: bool> TableT for EdDecompressTable<BUS> {
    fn name(&self) -> &'static str { "ed_decompress" }
    fn table(&self) -> Table { Table::ed_decompress() }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction { direction: BusDirection::Pull, multiplicity: BusMultiplicity::Column(COL_MULT), domainsep: BusData::Constant(LOGUP_EDDECOMPRESS_DOMAINSEP), data: vec![BusData::Column(COL_NU_A), BusData::Column(COL_NU_B), BusData::Column(COL_NU_C)] }];
        buses.extend(memory_lookups_consecutive(COL_NU_A, COL_A, 32));
        buses.extend(memory_lookups_consecutive(COL_NU_B, COL_OUT, N_OUT));
        let (u8s, u16s, u7s) = range_cols();
        buses.extend(range_lookups(&u8s, RANGE_U8));
        buses.extend(range_lookups(&u16s, RANGE_U16));
        buses.extend(range_lookups(&u7s, RANGE_U7));
        buses
    }
    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> { let mut row = vec![F::ZERO; N_COLS]; row[COL_NU_A] = F::from_usize(zero_vec_ptr); row[COL_NU_B] = F::from_usize(zero_vec_ptr); row }
    #[inline(always)]
    fn execute<M: MemoryAccess>(&self, arg_a: F, arg_b: F, _arg_c: F, _args: PrecompileCompTimeArgs<usize>, ctx: &mut InstructionContext<'_, M>) -> Result<(), RunnerError> {
        let a_ptr = arg_a.to_usize(); let out_ptr = arg_b.to_usize();
        let mut cells = [F::ZERO; 32]; ctx.memory.get_slice_into(a_ptr, &mut cells)?;
        let a: [u8; 32] = std::array::from_fn(|i| { let v = cells[i].as_canonical_u32(); assert!(v < 256, "ed_decompress: A limb is not a byte"); v as u8 });
        let row = make_row(&a, a_ptr, out_ptr);
        ctx.memory.set_slice(out_ptr, &row[COL_OUT..COL_OUT + N_OUT])?;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        for (i, v) in row.iter().enumerate() { trace.columns[i].push(*v); }
        Ok(())
    }
}

pub fn range_cols() -> (Vec<usize>, Vec<usize>, Vec<usize>) {
    let mut u8s = vec![]; let mut u16s = vec![];
    let rng = |v: &mut Vec<usize>, b: usize, n: usize| v.extend(b..b + n);
    rng(&mut u8s, COL_A, 32); rng(&mut u8s, COL_AX, 64); rng(&mut u8s, COL_NX, 32); rng(&mut u8s, COL_PMX, 32); rng(&mut u8s, COL_XCAN, 32);
    for b in [COL_T, COL_V, COL_W] { rng(&mut u8s, b, 32 + QL); rng(&mut u16s, b + 66, WL); }
    rng(&mut u8s, COL_OC, QL); rng(&mut u16s, COL_OC + QL, WL);
    rng(&mut u8s, COL_XLT, 32); rng(&mut u8s, COL_YLT, 32);
    (u8s, u16s, vec![COL_H, COL_HX])
}

pub fn make_row(a: &[u8; 32], a_ptr: usize, out_ptr: usize) -> [F; N_COLS] {
    let m = &P_25519; let fu = |b: u8| F::from_usize(b as usize);
    let mut row = [F::ZERO; N_COLS];
    row[COL_MULT] = F::ONE; row[COL_NU_A] = F::from_usize(a_ptr); row[COL_NU_B] = F::from_usize(out_ptr);
    for i in 0..32 { row[COL_A + i] = fu(a[i]); }
    let sign = a[31] >> 7; let h = a[31] & 0x7f;
    row[COL_H] = fu(h); row[COL_SIGN] = fu(sign);
    let mut y = *a; y[31] = h;
    let put_r = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
    let put_z = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..QL { row[base + i] = fu(w.q[i]); } for i in 0..WL { row[base + QL + i] = F::from_usize(w.w[i] as usize); } };
    let t = mod_mul(&y, &y, m); put_r(&mut row, COL_T, &make_identity(&[(&y, &y, true)], &[], false, m));
    let v = mod_mul(&D_LIMBS, &t, m); put_r(&mut row, COL_V, &make_identity(&[(&D_LIMBS, &t, true)], &[], false, m));
    let one = { let mut o = [0u8; 32]; o[0] = 1; o };
    let num = mod_sub(&t, &one, m); let den = mod_add(&one, &v, m);
    let x2 = mod_mul(&num, &mod_inv(&den, m), m);
    let x = sqrt_mod_p(&x2).expect("ed_decompress: A is not a valid point encoding");
    let xcan = if x[0] & 1 == 0 { x } else { mod_sub(&[0u8; 32], &x, m) };
    for i in 0..32 { row[COL_XCAN + i] = fu(xcan[i]); }
    put_r(&mut row, COL_W, &make_identity(&[(&xcan, &xcan, true)], &[], false, m));
    let w = mod_mul(&xcan, &xcan, m);
    put_z(&mut row, COL_OC, &make_identity(&[(&w, &v, true)], &[(&w, true), (&t, false), (&one, true)], true, m));
    let pm1: [i32; 32] = std::array::from_fn(|i| if i == 0 { P_25519[0] as i32 - 1 } else { P_25519[i] as i32 });
    let borrow_chain = |row: &mut [F; N_COLS], base: usize, minuend: &[i32; 32], sub: &[u8; 32]| { let mut bw = 0i32; for i in 0..32 { let mut d = minuend[i] - sub[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } row[base + i] = fu(d as u8); row[base + 32 + i] = fu(bw as u8); } assert_eq!(bw, 0); };
    borrow_chain(&mut row, COL_XLT, &pm1, &xcan);
    row[COL_HX] = fu(xcan[0] >> 1);
    let pmx = { let mut bw = 0i32; let mut out = [0u8; 32]; for i in 0..32 { let mut d = P_25519[i] as i32 - xcan[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } out[i] = d as u8; row[COL_NEG + i] = fu(bw as u8); } assert_eq!(bw, 0); out };
    let (ax, nx) = if sign == 1 { (pmx, xcan) } else { (xcan, pmx) };
    for i in 0..32 { row[COL_AX + i] = fu(ax[i]); row[COL_NX + i] = fu(nx[i]); row[COL_PMX + i] = fu(pmx[i]); }
    let ge = limbs_to_int(&y) >= modulus_int(m);
    row[COL_GE] = F::from_bool(ge);
    let ycan = if ge { let mut bw = 0i32; let mut out = [0u8; 32]; for i in 0..32 { let mut d = y[i] as i32 - P_25519[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } out[i] = d as u8; row[COL_YB + i] = fu(bw as u8); } assert_eq!(bw, 0); out } else { borrow_chain(&mut row, COL_YLT, &pm1, &y); y };
    for i in 0..32 { row[COL_YCAN + i] = fu(ycan[i]); }
    row
}

pub fn sqrt_mod_p(a: &[u8; 32]) -> Option<[u8; 32]> {
    let m = modulus_int(&P_25519); let ai = limbs_to_int(a).mod_floor(&m);
    if ai.is_zero() { return Some([0u8; 32]); }
    let e = (&m + BigInt::from(3)) >> 3usize;
    let mut r = ai.modpow(&e, &m);
    if (&r * &r).mod_floor(&m) != ai { let i = BigInt::from(2).modpow(&((&m - BigInt::from(1)) >> 2usize), &m); r = (r * i).mod_floor(&m); if (&r * &r).mod_floor(&m) != ai { return None; } }
    Some(int_to_limbs(&r, 32).try_into().unwrap())
}
pub fn compress(p: &Affine) -> [u8; 32] { let mut a = p.y; a[31] |= (p.x[0] & 1) << 7; a }
