//! T4 `ScalarL` as a VM table: `scalar_l(in_ptr, acc_ptr, out_ptr)`, one row per signature.
//!   reads  m[in_ptr  .. +100] = h (64 bytes, the SHA-512 digest) ‖ s (32 bytes) ‖ ρ (4 cells < p, 31 bits each)
//!   reads  m[acc_ptr .. +64]  = K_in (32 wide limbs) ‖ S_in (32 wide limbs)
//!   writes m[out_ptr .. +90]  = K_out ‖ S_out ‖ m_j (13) ‖ sgn_j (13)
//! proves c ≡ h (mod L), ρ = Σ_j cell_j·2^{31j} with each cell's 31-bit decomposition unique (value < p),
//! 13 signed 10-bit windows of ρ, k ≡ ρ·c, σ ≡ ρ·s (mod L), s < L, K_out = K_in + k, S_out = S_in + σ
//! limb-wise (the lazy accumulators are chained by the driver through memory: acc_ptr of row i+1 is
//! out_ptr of row i, whose first 64 cells are K_out ‖ S_out). Every arithmetic constraint is gated
//! by the multiplicity, so all-zero padding rows (pointers at the zero region) are valid.

use crate::execution::memory::MemoryAccess;
use crate::tables::ed25519::gadgets::*;
use crate::*;
use backend::*;
use num_bigint::BigInt;
use num_integer::Integer;

pub const SCALAR_L_NAME: &str = "scalar_l";
pub const LOGUP_SCALAR_L_DOMAINSEP: usize = 22;
pub use crate::tables::ed25519::ed_add_table::LOGUP_ROUTING_DOMAINSEP;
pub const RHO_BITS: usize = 124;
pub const RHO_CELLS: usize = 4;
pub const WINDOWS: usize = 13;

pub const COL_MULT: usize = 0;
pub const COL_NU_A: usize = 1;
pub const COL_NU_B: usize = 2;
pub const COL_NU_C: usize = 3;
pub const COL_IN: usize = 4;             // 101
pub const COL_HLO: usize = 4;
pub const COL_HHI: usize = 36;
pub const COL_S: usize = 68;
pub const COL_RHO: usize = 100;          // 4 cells
pub const COL_PTR: usize = 104;          // the R point record (EdSig output) this signature routes to T3
pub const N_IN: usize = 101;
pub const COL_ACC: usize = 105;          // 64
pub const COL_KIN: usize = 105;
pub const COL_SIN: usize = 137;
pub const COL_OUT: usize = 169;          // 90
pub const COL_KOUT: usize = 169;
pub const COL_SOUT: usize = 201;
pub const COL_M: usize = 233;
pub const COL_SGN: usize = 246;
pub const N_OUT: usize = 90;
pub const COL_C: usize = 259;            // 130 (r q w)
pub const COL_RHO_BITS: usize = 389;     // 124
pub const COL_BRW: usize = 513;          // 13
pub const COL_INV: usize = 526;          // 13
pub const COL_NZ: usize = 539;           // 13
pub const COL_K: usize = 552;            // 130
pub const COL_SIG: usize = 682;          // 130
pub const COL_SLT: usize = 812;          // 64
pub const COL_RU: usize = 876;           // 8
pub const COL_NSGN: usize = 884;         // 13: 1 − sgn_j (the MSM adds −R_i)
pub const N_COLS: usize = 897;

pub fn k256_limbs() -> [u8; 32] { let m = modulus_int(&L_25519); int_to_limbs(&(BigInt::from(1u8) << 256usize).mod_floor(&m), 32).try_into().unwrap() }

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ScalarLTable<const BUS: bool>;

impl<const BUS: bool> Air for ScalarLTable<BUS> {
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
        let ds = AB::IF::from_usize(LOGUP_SCALAR_L_DOMAINSEP);
        if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, mult.clone(), ds, &[nu_a, nu_b, nu_c]); }
        else { builder.declare_values(&[mult.clone()]); builder.declare_values(&[nu_a, nu_b, nu_c, ds]); }
        // routing pushes (j, m_j, 1 − sgn_j, ptr) with multiplicity nz_j → T3 bucket rows
        let route_ds = AB::IF::from_usize(LOGUP_ROUTING_DOMAINSEP);
        for j in 0..WINDOWS {
            let data = [AB::IF::from_usize(j), c[COL_M + j].clone(), c[COL_NSGN + j].clone(), c[COL_PTR].clone()];
            if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, c[COL_NZ + j].clone(), route_ds.clone(), &data); }
            else { builder.declare_values(&[c[COL_NZ + j].clone()]); builder.declare_values(&[data[0].clone(), data[1].clone(), data[2].clone(), data[3].clone(), route_ds.clone()]); }
        }
        builder.assert_bool(mult.clone());
        for j in 0..WINDOWS { builder.assert_zero(mult.clone() * (c[COL_NSGN + j].clone() + c[COL_SGN + j].clone() - AB::IF::ONE)); } // gated: padding rows are all zero
        // SOUNDNESS: an inactive row (mult=0) must route nothing, else a padding row injects an
        // arbitrary (scalar, point) into the MSM — a universal forgery. nz is boolean, so this forces nz=0.
        for j in 0..WINDOWS { builder.assert_zero((AB::IF::ONE - mult.clone()) * c[COL_NZ + j].clone()); }
        let g = mult.clone();
        let sl = |base: usize, n: usize| -> Vec<AB::IF> { c[base..base + n].to_vec() };
        let hints_r = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };
        let k256: Vec<AB::IF> = k256_limbs().iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        // 1. c ≡ h_lo + h_hi·K256 (mod L)
        let (hlo, hhi) = (sl(COL_HLO, 32), sl(COL_HHI, 32));
        let (cv, hc) = hints_r(COL_C);
        eval_identity(builder, &g, &[(&hhi, &k256, true)], &[(&hlo, true)], &hc, &L_25519);
        // 2. ρ bits boolean; cell_j = Σ_{t<31} bit_{31j+t}·2^t, unique (value < p): top 7 bits all one ⇒ low 24 bits zero
        let bits = sl(COL_RHO_BITS, RHO_BITS);
        for b in &bits { builder.assert_bool(b.clone()); }
        for j in 0..RHO_CELLS {
            let mut cell = AB::IF::ZERO;
            for t in 0..31 { cell += bits[31 * j + t].clone() * f(1 << t); }
            builder.assert_zero(g.clone() * (c[COL_RHO + j].clone() - cell));
            let b = |t: usize| bits[31 * j + t].clone();
            let t1 = c[COL_RU + 2 * j].clone(); let top = c[COL_RU + 2 * j + 1].clone();
            builder.assert_zero(t1.clone() - b(24) * b(25) * b(26) * b(27));
            builder.assert_zero(top.clone() - t1 * b(28) * b(29) * b(30));
            let mut low = AB::IF::ZERO;
            for t in 0..24 { low += b(t) * f(1 << t); }
            builder.assert_zero(top * low);
        }
        let mut rho_limbs: Vec<AB::IF> = (0..32).map(|_| AB::IF::ZERO).collect();
        for (i, b) in bits.iter().enumerate() { rho_limbs[i / 8] += b.clone() * f(1 << (i % 8)); }
        let window = |j: usize| -> AB::IF { let mut acc = AB::IF::ZERO; for t in 0..10 { let i = 10 * j + t; if i < RHO_BITS { acc += bits[i].clone() * f(1 << t); } } acc };
        // 3. signed recoding: w_j + b_{j−1} = (1 − 2s_j)·m_j + 1024·b_j ; nz_j = [m_j ≠ 0]; b_12 = 0
        for j in 0..WINDOWS {
            let (m, s, b, inv, nz) = (c[COL_M + j].clone(), c[COL_SGN + j].clone(), c[COL_BRW + j].clone(), c[COL_INV + j].clone(), c[COL_NZ + j].clone());
            let b_prev = if j == 0 { AB::IF::ZERO } else { c[COL_BRW + j - 1].clone() };
            builder.assert_bool(s.clone()); builder.assert_bool(b.clone()); builder.assert_bool(nz.clone());
            builder.assert_zero(g.clone() * (window(j) + b_prev - (one.clone() - s.double()) * m.clone() - b.clone() * f(1024)));
            builder.assert_zero(m.clone() * inv - nz.clone());
            builder.assert_zero((one.clone() - nz) * m);
        }
        builder.assert_zero(c[COL_BRW + WINDOWS - 1].clone());
        // 4. k ≡ ρ·c, σ ≡ ρ·s (mod L)
        let (kv, hk) = hints_r(COL_K); eval_identity(builder, &g, &[(&rho_limbs, &cv, true)], &[], &hk, &L_25519);
        let s = sl(COL_S, 32);
        let (sig, hs) = hints_r(COL_SIG); eval_identity(builder, &g, &[(&rho_limbs, &s, true)], &[], &hs, &L_25519);
        // 5. s ≤ L − 1
        let diff = sl(COL_SLT, 32); let bw = sl(COL_SLT + 32, 32);
        for i in 0..32 {
            let lm1 = if i == 0 { L_25519[0] as usize - 1 } else { L_25519[i] as usize };
            let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(g.clone() * (AB::IF::from_usize(lm1) - s[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256)));
            builder.assert_bool(bw[i].clone());
        }
        builder.assert_zero(bw[31].clone());
        // 6. lazy accumulators through memory
        for i in 0..32 {
            builder.assert_zero(c[COL_KOUT + i].clone() - c[COL_KIN + i].clone() - kv[i].clone());
            builder.assert_zero(c[COL_SOUT + i].clone() - c[COL_SIN + i].clone() - sig[i].clone());
        }
    }
}
// bus 2 + mult 1 + c 65 + bits 124 + cells 4 + uniqueness 12 + windows 13×6 + 1 + k 65 + σ 65 + s<L 65 + acc 64
pub const N_CONSTRAINTS: usize = 2 + 2 * WINDOWS + 1 + WINDOWS + WINDOWS + 65 + 124 + 4 + 12 + 13 * 6 + 1 + 65 + 65 + 65 + 64;

impl<const BUS: bool> TableT for ScalarLTable<BUS> {
    fn name(&self) -> &'static str { "scalar_l" }
    fn table(&self) -> Table { Table::scalar_l() }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let mut buses = vec![BusInteraction {
            direction: BusDirection::Pull,
            multiplicity: BusMultiplicity::Column(COL_MULT),
            domainsep: BusData::Constant(LOGUP_SCALAR_L_DOMAINSEP),
            data: vec![BusData::Column(COL_NU_A), BusData::Column(COL_NU_B), BusData::Column(COL_NU_C)],
        }];
        for j in 0..WINDOWS {
            buses.push(BusInteraction { direction: BusDirection::Push, multiplicity: BusMultiplicity::Column(COL_NZ + j), domainsep: BusData::Constant(LOGUP_ROUTING_DOMAINSEP), data: vec![BusData::Constant(j), BusData::Column(COL_M + j), BusData::Column(COL_NSGN + j), BusData::Column(COL_PTR)] });
        }
        buses.extend(memory_lookups_consecutive(COL_NU_A, COL_IN, N_IN));
        buses.extend(memory_lookups_consecutive(COL_NU_B, COL_ACC, 64));
        buses.extend(memory_lookups_consecutive(COL_NU_C, COL_OUT, N_OUT));
        for (section, cols) in range_cols() { buses.extend(range_lookups(&cols, section)); }
        buses
    }
    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; N_COLS];
        for c in [COL_NU_A, COL_NU_B, COL_NU_C] { row[c] = F::from_usize(zero_vec_ptr); }
        row
    }
    #[inline(always)]
    fn execute<M: MemoryAccess>(&self, arg_a: F, arg_b: F, arg_c: F, _args: PrecompileCompTimeArgs<usize>, ctx: &mut InstructionContext<'_, M>) -> Result<(), RunnerError> {
        let (in_ptr, acc_ptr, out_ptr) = (arg_a.to_usize(), arg_b.to_usize(), arg_c.to_usize());
        let mut inp = [F::ZERO; N_IN]; ctx.memory.get_slice_into(in_ptr, &mut inp)?;
        let mut acc = [F::ZERO; 64]; ctx.memory.get_slice_into(acc_ptr, &mut acc)?;
        let byte = |x: F| -> u8 { let v = x.as_canonical_u32(); assert!(v < 256, "scalar_l: input cell is not a byte"); v as u8 };
        let h: [u8; 64] = std::array::from_fn(|i| byte(inp[i]));
        let s: [u8; 32] = std::array::from_fn(|i| byte(inp[64 + i]));
        let rho: [u32; 4] = std::array::from_fn(|j| inp[96 + j].as_canonical_u32());
        let k_in: [u64; 32] = std::array::from_fn(|i| acc[i].as_canonical_u32() as u64);
        let s_in: [u64; 32] = std::array::from_fn(|i| acc[32 + i].as_canonical_u32() as u64);
        let row = make_row(&h, &s, &rho, &k_in, &s_in, inp[100].to_usize(), in_ptr, acc_ptr, out_ptr);
        ctx.memory.set_slice(out_ptr, &row[COL_OUT..COL_OUT + N_OUT])?;
        let trace = ctx.traces.get_mut(&self.table()).unwrap();
        for (i, v) in row.iter().enumerate() { trace.columns[i].push(*v); }
        Ok(())
    }
}

/// Range classes. h, s, identity r/q limbs and the s<L diffs are bytes; witness limbs u16; windows u10.
/// ρ cells are decomposed; K/S limbs are bounded by the driver's chain; bits/flags are boolean.
pub fn range_cols() -> Vec<(usize, Vec<usize>)> {
    let mut u8s: Vec<usize> = vec![]; let mut u16s: Vec<usize> = vec![];
    u8s.extend(COL_HLO..COL_HLO + 64); u8s.extend(COL_S..COL_S + 32); u8s.extend(COL_SLT..COL_SLT + 32);
    for b in [COL_C, COL_K, COL_SIG] { u8s.extend(b..b + 32 + QL); u16s.extend(b + 66..b + 66 + WL); }
    vec![(RANGE_U8, u8s), (RANGE_U16, u16s), (RANGE_U10, (COL_M..COL_M + WINDOWS).collect())]
}

pub fn rho_from_cells(cells: &[u32; 4]) -> u128 { cells.iter().enumerate().fold(0u128, |acc, (j, &c)| acc | ((c as u128) << (31 * j))) }

pub fn make_row(h: &[u8; 64], s: &[u8; 32], rho_cells: &[u32; 4], k_in: &[u64; 32], s_in: &[u64; 32], point_ptr: usize, in_ptr: usize, acc_ptr: usize, out_ptr: usize) -> [F; N_COLS] {
    let fu = |b: u8| F::from_usize(b as usize);
    let l = &L_25519; let k256 = k256_limbs();
    let mut row = [F::ZERO; N_COLS];
    row[COL_MULT] = F::ONE;
    row[COL_NU_A] = F::from_usize(in_ptr); row[COL_NU_B] = F::from_usize(acc_ptr); row[COL_NU_C] = F::from_usize(out_ptr);
    let hlo: [u8; 32] = h[..32].try_into().unwrap(); let hhi: [u8; 32] = h[32..].try_into().unwrap();
    for i in 0..32 { row[COL_HLO + i] = fu(hlo[i]); row[COL_HHI + i] = fu(hhi[i]); row[COL_S + i] = fu(s[i]); }
    row[COL_PTR] = F::from_usize(point_ptr);
    for j in 0..4 { assert!((rho_cells[j] as u64) < F::ORDER_U64, "scalar_l: ρ cell must be a field element"); row[COL_RHO + j] = F::from_usize(rho_cells[j] as usize); }
    for i in 0..32 { row[COL_KIN + i] = F::from_usize(k_in[i] as usize); row[COL_SIN + i] = F::from_usize(s_in[i] as usize); }
    let put = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
    let wc = make_identity(&[(&hhi, &k256, true)], &[(&hlo, true)], false, l);
    put(&mut row, COL_C, &wc);
    let rho = rho_from_cells(rho_cells);
    for i in 0..RHO_BITS { row[COL_RHO_BITS + i] = F::from_bool((rho >> i) & 1 == 1); }
    for j in 0..4 {
        let b = |t: usize| ((rho_cells[j] >> t) & 1) as usize;
        let t1 = b(24) * b(25) * b(26) * b(27); let top = t1 * b(28) * b(29) * b(30);
        row[COL_RU + 2 * j] = F::from_usize(t1); row[COL_RU + 2 * j + 1] = F::from_usize(top);
    }
    let mut rho_limbs = [0u8; 32]; for i in 0..16 { rho_limbs[i] = ((rho >> (8 * i)) & 255) as u8; }
    let mut borrow = 0i64;
    for j in 0..WINDOWS {
        let w = ((rho >> (10 * j)) & 1023) as i64 + borrow;
        let (m, sgn, b) = if w > 512 { (1024 - w, 1, 1) } else { (w, 0, 0) };
        borrow = b;
        row[COL_M + j] = F::from_usize(m as usize); row[COL_SGN + j] = fu(sgn as u8); row[COL_BRW + j] = fu(b as u8);
        row[COL_NZ + j] = F::from_bool(m != 0); row[COL_INV + j] = if m != 0 { F::from_usize(m as usize).inverse() } else { F::ZERO };
        row[COL_NSGN + j] = F::ONE - row[COL_SGN + j];
    }
    assert_eq!(borrow, 0);
    let wk = make_identity(&[(&rho_limbs, &wc.r, true)], &[], false, l); put(&mut row, COL_K, &wk);
    let ws = make_identity(&[(&rho_limbs, s, true)], &[], false, l); put(&mut row, COL_SIG, &ws);
    {
        let mut bw = 0i32;
        for i in 0..32 {
            let lm1 = if i == 0 { L_25519[0] as i32 - 1 } else { L_25519[i] as i32 };
            let mut d = lm1 - s[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; }
            row[COL_SLT + i] = fu(d as u8); row[COL_SLT + 32 + i] = fu(bw as u8);
        }
        assert_eq!(bw, 0, "scalar_l: s must be < L");
    }
    for i in 0..32 { row[COL_KOUT + i] = F::from_usize(k_in[i] as usize + wk.r[i] as usize); row[COL_SOUT + i] = F::from_usize(s_in[i] as usize + ws.r[i] as usize); }
    row
}
