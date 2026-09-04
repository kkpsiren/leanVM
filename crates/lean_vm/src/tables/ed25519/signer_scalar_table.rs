//! T7 `SignerScalar` as a VM table: `signer_scalar(k_ptr, out_ptr, 0)`, one row per signer (and one
//! for the leaf's S): reads K (32 wide limbs at k_ptr, the lazy sum chained through T4 rows), proves
//! K_red ≡ K (mod L) with the wide-limb identity, K_red's 253 bits and 26 signed 10-bit windows;
//! writes m[out_ptr .. +84] = K_red (32) ‖ m_j (26) ‖ sgn_j (26). Gated by the multiplicity.

use crate::execution::memory::MemoryAccess;
use crate::tables::ed25519::gadgets::*;
use crate::*;
use backend::*;
use num_bigint::BigInt;

pub const SIGNER_SCALAR_NAME: &str = "signer_scalar";
pub const LOGUP_SIGNER_SCALAR_DOMAINSEP: usize = 26;
pub use crate::tables::ed25519::ed_add_table::LOGUP_ROUTING_DOMAINSEP;
pub const T7_WINDOWS: usize = 26;

pub const COL_MULT: usize = 0;
pub const COL_NU_A: usize = 1;
pub const COL_NU_B: usize = 2;
pub const COL_NU_C: usize = 3;
pub const COL_K: usize = 4;              // 32 wide limbs
pub const COL_PTR: usize = 36;           // the point record (A from EdDecompress, or the base point) to route to T3
pub const COL_FLIP: usize = 37;          // 1: negate the point (A rows), 0: as is (the S row on B)
pub const N_IN: usize = 34;
pub const COL_OUT: usize = 38;           // 84
pub const COL_KRED: usize = 38;          // 32 (r of the identity)
pub const COL_M: usize = 70;             // 26
pub const COL_SGN: usize = 96;           // 26
pub const N_OUT: usize = 84;
pub const COL_QW: usize = 122;           // 98: q (34) w (64)
pub const COL_BITS: usize = 220;         // 253
pub const COL_BRW: usize = 473;          // 26
pub const COL_INV: usize = 499;          // 26
pub const COL_NZ: usize = 525;           // 26
pub const COL_PSGN: usize = 551;         // 26: sgn_j ⊕ flip, the sign pushed to T3
pub const N_COLS: usize = 577;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SignerScalarTable<const BUS: bool>;

impl<const BUS: bool> Air for SignerScalarTable<BUS> {
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
        let ds = AB::IF::from_usize(LOGUP_SIGNER_SCALAR_DOMAINSEP);
        if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, mult.clone(), ds, &[nu_a, nu_b, nu_c.clone()]); }
        else { builder.declare_values(&[mult.clone()]); builder.declare_values(&[nu_a, nu_b, nu_c.clone(), ds]); }
        let route_ds = AB::IF::from_usize(LOGUP_ROUTING_DOMAINSEP);
        for j in 0..T7_WINDOWS {
            let data = [AB::IF::from_usize(j), c[COL_M + j].clone(), c[COL_PSGN + j].clone(), c[COL_PTR].clone()];
            if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, c[COL_NZ + j].clone(), route_ds.clone(), &data); }
            else { builder.declare_values(&[c[COL_NZ + j].clone()]); builder.declare_values(&[data[0].clone(), data[1].clone(), data[2].clone(), data[3].clone(), route_ds.clone()]); }
        }
        builder.assert_bool(mult.clone()); builder.assert_zero(nu_c);
        let flip = c[COL_FLIP].clone(); builder.assert_bool(flip.clone());
        for j in 0..T7_WINDOWS { let sg = c[COL_SGN + j].clone(); builder.assert_zero(c[COL_PSGN + j].clone() - (sg.clone() + flip.clone() - (sg * flip.clone()).double())); }
        let g = mult.clone();
        let k: Vec<AB::IF> = c[COL_K..COL_K + 32].to_vec();
        let hk = HintCols { r: Some(&c[COL_KRED..COL_KRED + 32]), q: &c[COL_QW..COL_QW + QL], w: &c[COL_QW + QL..COL_QW + QL + WL] };
        eval_identity(builder, &g, &[], &[(&k, true)], &hk, &L_25519);
        let kred: Vec<AB::IF> = c[COL_KRED..COL_KRED + 32].to_vec();
        let bits: Vec<AB::IF> = c[COL_BITS..COL_BITS + 253].to_vec();
        for b in &bits { builder.assert_bool(b.clone()); }
        for i in 0..32 { let mut acc = AB::IF::ZERO; for t in 0..8 { let bi = 8 * i + t; if bi < 253 { acc += bits[bi].clone() * f(1 << t); } } builder.assert_zero(kred[i].clone() - acc); }
        let window = |j: usize| -> AB::IF { let mut acc = AB::IF::ZERO; for t in 0..10 { let i = 10 * j + t; if i < 253 { acc += bits[i].clone() * f(1 << t); } } acc };
        for j in 0..T7_WINDOWS {
            let (m, s, b, inv, nz) = (c[COL_M + j].clone(), c[COL_SGN + j].clone(), c[COL_BRW + j].clone(), c[COL_INV + j].clone(), c[COL_NZ + j].clone());
            let b_prev = if j == 0 { AB::IF::ZERO } else { c[COL_BRW + j - 1].clone() };
            builder.assert_bool(s.clone()); builder.assert_bool(b.clone()); builder.assert_bool(nz.clone());
            builder.assert_zero(window(j) + b_prev - (one.clone() - s.double()) * m.clone() - b.clone() * f(1024));
            builder.assert_zero(m.clone() * inv - nz.clone());
            builder.assert_zero((one.clone() - nz) * m);
        }
        builder.assert_zero(c[COL_BRW + T7_WINDOWS - 1].clone());
    }
}
// bus 2 + mult/nu_c 2 + identity 65 + bits 253 + recompose 32 + windows 26×6 + 1
pub const N_CONSTRAINTS: usize = 2 + 2 * T7_WINDOWS + 2 + 1 + T7_WINDOWS + 65 + 253 + 32 + 26 * 6 + 1;

impl<const BUS: bool> TableT for SignerScalarTable<BUS> {
    fn name(&self) -> &'static str { "signer_scalar" }
    fn table(&self) -> Table { Table::signer_scalar() }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(COL_MULT),
            domainsep: BusData::Constant(LOGUP_SIGNER_SCALAR_DOMAINSEP),
            data: vec![BusData::Column(COL_NU_A), BusData::Column(COL_NU_B), BusData::Column(COL_NU_C)],
        }];
        for j in 0..T7_WINDOWS {
            buses.push(BusInteraction { direction: BusDirection::Push, multiplicity: BusMultiplicity::Column(COL_NZ + j), domainsep: BusData::Constant(LOGUP_ROUTING_DOMAINSEP), data: vec![BusData::Constant(j), BusData::Column(COL_M + j), BusData::Column(COL_PSGN + j), BusData::Column(COL_PTR)] });
        }
        buses.extend(memory_lookups_consecutive(COL_NU_A, COL_K, N_IN));
        buses.extend(memory_lookups_consecutive(COL_NU_B, COL_OUT, N_OUT));
        for (section, cols) in range_cols() { buses.extend(range_lookups(&cols, section)); }
        buses
    }
    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; N_COLS];
        row[COL_NU_A] = F::from_usize(zero_vec_ptr); row[COL_NU_B] = F::from_usize(zero_vec_ptr);
        row
    }
    #[inline(always)]
    fn execute<M: MemoryAccess>(&self, arg_a: F, arg_b: F, arg_c: F, _args: PrecompileCompTimeArgs<usize>, ctx: &mut InstructionContext<'_, M>) -> Result<(), RunnerError> {
        let (k_ptr, out_ptr) = (arg_a.to_usize(), arg_b.to_usize());
        let mut cells = [F::ZERO; N_IN]; ctx.memory.get_slice_into(k_ptr, &mut cells)?;
        let k: [i64; 32] = std::array::from_fn(|i| cells[i].as_canonical_u32() as i64);
        let row = make_row(&k, cells[32].to_usize(), cells[33].as_canonical_u32() != 0, k_ptr, out_ptr);
        ctx.memory.set_slice(out_ptr, &row[COL_OUT..COL_OUT + N_OUT])?;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        for (i, v) in row.iter().enumerate() { trace.columns[i].push(*v); }
        let _ = arg_c;
        Ok(())
    }
}

/// Range classes: quotient limbs bytes, witness limbs u16, windows u10. K limbs are bounded by the
/// driver's chain; K_red is recomposed from boolean bits.
pub fn range_cols() -> Vec<(usize, Vec<usize>)> {
    vec![(RANGE_U8, (COL_QW..COL_QW + QL).collect()), (RANGE_U16, (COL_QW + QL..COL_QW + QL + WL).collect()), (RANGE_U10, (COL_M..COL_M + T7_WINDOWS).collect())]
}

pub fn make_row(k_wide: &[i64; 32], point_ptr: usize, flip: bool, k_ptr: usize, out_ptr: usize) -> [F; N_COLS] {
    let mut row = [F::ZERO; N_COLS];
    row[COL_MULT] = F::ONE; row[COL_NU_A] = F::from_usize(k_ptr); row[COL_NU_B] = F::from_usize(out_ptr);
    row[COL_PTR] = F::from_usize(point_ptr); row[COL_FLIP] = F::from_bool(flip);
    for i in 0..32 { assert!(k_wide[i] >= 0 && k_wide[i] < (1 << 21), "signer_scalar: K limb out of the lazy-sum bound"); row[COL_K + i] = F::from_usize(k_wide[i] as usize); }
    let w = make_identity_wide(&[], &[(k_wide, true)], false, &L_25519);
    for i in 0..32 { row[COL_KRED + i] = F::from_usize(w.r[i] as usize); }
    for i in 0..QL { row[COL_QW + i] = F::from_usize(w.q[i] as usize); }
    for i in 0..WL { row[COL_QW + QL + i] = F::from_usize(w.w[i] as usize); }
    let kred = limbs_to_int(&w.r);
    for i in 0..253 { row[COL_BITS + i] = F::from_bool(((&kred >> i) & BigInt::from(1)) == BigInt::from(1)); }
    let mut borrow = 0i64;
    for j in 0..T7_WINDOWS {
        let wv: i64 = ((&kred >> (10 * j)) & BigInt::from(1023)).try_into().unwrap();
        let wv = wv + borrow;
        let (m, sgn, b) = if wv > 512 { (1024 - wv, 1, 1) } else { (wv, 0, 0) };
        borrow = b;
        row[COL_M + j] = F::from_usize(m as usize); row[COL_SGN + j] = F::from_usize(sgn as usize); row[COL_BRW + j] = F::from_usize(b as usize);
        row[COL_NZ + j] = F::from_bool(m != 0); row[COL_INV + j] = if m != 0 { F::from_usize(m as usize).inverse() } else { F::ZERO };
        row[COL_PSGN + j] = F::from_bool((sgn == 1) != flip);
    }
    assert_eq!(borrow, 0, "window 25 has 3 bits: no final borrow");
    row
}
