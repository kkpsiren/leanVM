//! T3 `EdAdd` as a VM table (spec §3.3 adapted to the memory interconnect): one row = one complete
//! affine twisted-Edwards addition acc_out = acc_in + P, chains laid out in REVERSE row order (the
//! head holds the total and reads its input from the next row; a tail has `start = 1` and
//! acc_in = (0,1)). No execution-bus anchor: the trace is a post-pass over the routing tuples
//! pushed by ScalarL/SignerScalar (`fill_trace_ed_add`), the points are looked up in memory.
//!
//! Row kinds (one-hot on active rows):
//!   bucket : pulls a routing tuple (j, b, s, ptr) (mult 1); P = the point at ptr (x at +0 or, for
//!            s = 1, the negated x at +65; y at +32) via memory lookups; the head pushes the bucket
//!            total (j, b, chunk_k) k = 0..5 (11 bytes of x3‖y3 per chunk).
//!   red1   : per window, b = 512 → 1 (start·(b−512) = 0, next.b = b + 1 in layout, head·(b−1) = 0):
//!            pulls the bucket total (j, b, ·) unless `empty` (then P = (0,1)); pushes (j, b, S_b).
//!   red2   : same shape; pulls (j, b, S_b); the head pushes (j, T_j).
//!   horner : one chain, j = 25 → 0 in evaluation order: an add row (cnt = 0) pulls (j, T_j), then
//!            10 doubling rows (cnt = 10 → 1, P = acc_in); the head is the `final` row (j = 0,
//!            cnt = 0) and zero-checks x3 ≡ 0, y3 ≡ 1 (mod p).
//! Every chain tail pushes a token, every head pulls one (#heads = #tails); inactive rows are
//! singletons (start = head = 1) with every multiplicity 0. Identities are gated by `active`.

use crate::tables::ed25519::curve::*;
use crate::tables::ed25519::gadgets::*;
use crate::*;
use backend::*;
use std::collections::BTreeMap;

pub const LOGUP_ROUTING_DOMAINSEP: usize = 82;
pub const LOGUP_BUCKET_FINAL_DOMAINSEP: usize = 86;
pub const LOGUP_RED1_OUT_DOMAINSEP: usize = 90;
pub const LOGUP_TJ_DOMAINSEP: usize = 94;
pub const LOGUP_TOKEN_DOMAINSEP: usize = 98;
pub const N_WINDOWS: usize = 26;
pub const N_BUCKETS: usize = 512;
pub const N_CHUNKS: usize = 6;
pub const CHUNK: usize = 11;
pub const N_DBL: usize = 10;
pub const POINT_NX_OFFSET: usize = 65; // x at +0, y at +32, negated x at +65 (EdSig / EdDecompress records)

// shift columns first
pub const COL_X3: usize = 0;
pub const COL_Y3: usize = 32;
pub const COL_HEAD: usize = 64;
pub const COL_J: usize = 65;
pub const COL_B: usize = 66;
pub const COL_ACTIVE: usize = 67;
pub const COL_KB: usize = 68;
pub const COL_KR1: usize = 69;
pub const COL_KR2: usize = 70;
pub const COL_KH: usize = 71;
pub const COL_CNT: usize = 72;
pub const N_SHIFT: usize = 73;
// flat
pub const COL_START: usize = 73;
pub const COL_EMPTY: usize = 74;
pub const COL_SGN: usize = 75;
pub const COL_PTR: usize = 76;
pub const COL_PXPTR: usize = 77;
pub const COL_PYPTR: usize = 78;
pub const COL_DBL: usize = 79;
pub const COL_INV0: usize = 80;
pub const COL_IS10: usize = 81;
pub const COL_INV10: usize = 82;
pub const COL_MROUTE: usize = 83;
pub const COL_MBFP: usize = 84;
pub const COL_MR1PULL: usize = 85;
pub const COL_MR1: usize = 86;
pub const COL_MR2: usize = 87;
pub const COL_MTJ: usize = 88;
pub const COL_MHA: usize = 89;
pub const COL_MTOKP: usize = 90;
pub const COL_MTOKQ: usize = 91;
pub const COL_PX_MEM: usize = 92;        // 32
pub const COL_PY_MEM: usize = 124;       // 32
pub const COL_PX: usize = 156;           // 32
pub const COL_PY: usize = 188;           // 32
pub const COL_T1: usize = 220;           // 130 (r q w)
pub const COL_T2: usize = 350;
pub const COL_F: usize = 480;
pub const COL_G: usize = 610;
pub const COL_X3H: usize = 740;          // 98 (q w)
pub const COL_Y3H: usize = 838;
pub const COL_ZX: usize = 936;           // 98: final zero-check x3 ≡ 0
pub const COL_ZY: usize = 1034;          // 98: final zero-check y3 − 1 ≡ 0
pub const N_COLS: usize = 1132;
pub const N_COLUMN_BUSES: usize = 1 + 6 * N_CHUNKS + 2;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EdAddTable<const BUS: bool>;

/// chunk k of the 64-cell buffer x‖y (constant zero beyond the end)
fn chunk_exprs<T: Clone + PrimeCharacteristicRing>(x: &[T], y: &[T], k: usize) -> Vec<T> {
    (0..CHUNK).map(|t| { let i = CHUNK * k + t; if i < 32 { x[i].clone() } else if i < 64 { y[i - 32].clone() } else { T::ZERO } }).collect()
}
fn chunk_data(x_col: usize, y_col: usize, k: usize) -> Vec<BusData> {
    (0..CHUNK).map(|t| { let i = CHUNK * k + t; if i < 32 { BusData::Column(x_col + i) } else if i < 64 { BusData::Column(y_col + i - 32) } else { BusData::Constant(0) } }).collect()
}

impl<const BUS: bool> Air for EdAddTable<BUS> {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 4 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { N_SHIFT }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let nx: Vec<AB::IF> = builder.shift().to_vec();
        let one = AB::IF::ONE;
        let f = |x: usize| AB::F::from_usize(x);
        let col = |i: usize| c[i].clone();
        let (start, head, active, empty, sgn) = (col(COL_START), col(COL_HEAD), col(COL_ACTIVE), col(COL_EMPTY), col(COL_SGN));
        let (kb, kr1, kr2, kh, cnt, dbl, is10) = (col(COL_KB), col(COL_KR1), col(COL_KR2), col(COL_KH), col(COL_CNT), col(COL_DBL), col(COL_IS10));
        let (j, b) = (col(COL_J), col(COL_B));
        let x3: Vec<AB::IF> = c[COL_X3..COL_X3 + 32].to_vec(); let y3: Vec<AB::IF> = c[COL_Y3..COL_Y3 + 32].to_vec();
        let px: Vec<AB::IF> = c[COL_PX..COL_PX + 32].to_vec(); let py: Vec<AB::IF> = c[COL_PY..COL_PY + 32].to_vec();

        // ---- buses (Column-multiplicity, in bus_interactions() order) ----
        let mut bus = |builder: &mut AB, mult: AB::IF, ds: usize, data: Vec<AB::IF>| {
            let ds = AB::IF::from_usize(ds);
            if BUS { eval_bus_virtual::<AB, EF>(builder, extra_data, mult, ds, &data); }
            else { builder.declare_values(&[mult]); let mut d = data; d.push(ds); builder.declare_values(&d); }
        };
        bus(builder, col(COL_MROUTE), LOGUP_ROUTING_DOMAINSEP, vec![j.clone(), b.clone(), sgn.clone(), col(COL_PTR)]);
        for k in 0..N_CHUNKS { let mut d = vec![j.clone(), b.clone(), AB::IF::from_usize(k)]; d.extend(chunk_exprs(&x3, &y3, k)); bus(builder, col(COL_MBFP), LOGUP_BUCKET_FINAL_DOMAINSEP, d); }
        for k in 0..N_CHUNKS { let mut d = vec![j.clone(), b.clone(), AB::IF::from_usize(k)]; d.extend(chunk_exprs(&px, &py, k)); bus(builder, col(COL_MR1PULL), LOGUP_BUCKET_FINAL_DOMAINSEP, d); }
        for k in 0..N_CHUNKS { let mut d = vec![j.clone(), b.clone(), AB::IF::from_usize(k)]; d.extend(chunk_exprs(&x3, &y3, k)); bus(builder, col(COL_MR1), LOGUP_RED1_OUT_DOMAINSEP, d); }
        for k in 0..N_CHUNKS { let mut d = vec![j.clone(), b.clone(), AB::IF::from_usize(k)]; d.extend(chunk_exprs(&px, &py, k)); bus(builder, col(COL_MR2), LOGUP_RED1_OUT_DOMAINSEP, d); }
        for k in 0..N_CHUNKS { let mut d = vec![j.clone(), AB::IF::from_usize(k)]; d.extend(chunk_exprs(&x3, &y3, k)); bus(builder, col(COL_MTJ), LOGUP_TJ_DOMAINSEP, d); }
        for k in 0..N_CHUNKS { let mut d = vec![j.clone(), AB::IF::from_usize(k)]; d.extend(chunk_exprs(&px, &py, k)); bus(builder, col(COL_MHA), LOGUP_TJ_DOMAINSEP, d); }
        bus(builder, col(COL_MTOKP), LOGUP_TOKEN_DOMAINSEP, vec![active.clone()]);
        bus(builder, col(COL_MTOKQ), LOGUP_TOKEN_DOMAINSEP, vec![active.clone()]);

        // ---- flags ----
        for x in [&start, &empty, &sgn, &active, &head, &kb, &kr1, &kr2, &kh, &dbl, &is10] { builder.assert_bool(x.clone()); }
        builder.assert_zero(kb.clone() + kr1.clone() + kr2.clone() + kh.clone() - active.clone());
        builder.assert_zero((one.clone() - active.clone()) * (one.clone() - start.clone()));
        builder.assert_zero((one.clone() - active.clone()) * (one.clone() - head.clone()));
        // multiplicity columns
        builder.assert_zero(col(COL_MROUTE) - active.clone() * kb.clone());
        builder.assert_zero(col(COL_MBFP) - active.clone() * kb.clone() * head.clone());
        builder.assert_zero(col(COL_MR1PULL) - active.clone() * kr1.clone() * (one.clone() - empty.clone()));
        builder.assert_zero(col(COL_MR1) - active.clone() * kr1.clone());
        builder.assert_zero(col(COL_MR2) - active.clone() * kr2.clone());
        builder.assert_zero(col(COL_MTJ) - active.clone() * kr2.clone() * head.clone());
        builder.assert_zero(col(COL_MHA) - active.clone() * kh.clone() * (one.clone() - dbl.clone()));
        builder.assert_zero(col(COL_MTOKP) - active.clone() * start.clone());
        builder.assert_zero(col(COL_MTOKQ) - active.clone() * head.clone());
        builder.assert_zero(empty.clone() * (one.clone() - kr1.clone()));

        // ---- chain continuity (next row = the previous step) ----
        let cont = one.clone() - start.clone();
        builder.assert_zero(cont.clone() * (one.clone() - kh.clone()) * (nx[COL_J].clone() - j.clone()));
        builder.assert_zero(cont.clone() * (nx[COL_ACTIVE].clone() - active.clone()));
        for k in [COL_KB, COL_KR1, COL_KR2, COL_KH] { builder.assert_zero(cont.clone() * (nx[k].clone() - c[k].clone())); }
        builder.assert_zero(cont.clone() * nx[COL_HEAD].clone());
        builder.assert_zero(start.clone() * (one.clone() - nx[COL_HEAD].clone()));
        let red = kr1.clone() + kr2.clone();
        builder.assert_zero(cont.clone() * kb.clone() * (nx[COL_B].clone() - b.clone()));
        builder.assert_zero(cont.clone() * red.clone() * (nx[COL_B].clone() - b.clone() - one.clone()));
        builder.assert_zero(start.clone() * red.clone() * (b.clone() - f(N_BUCKETS)));
        builder.assert_zero(head.clone() * red.clone() * (b.clone() - one.clone()));

        // ---- horner shape ----
        builder.assert_zero(cnt.clone() * col(COL_INV0) - dbl.clone());
        builder.assert_zero((one.clone() - dbl.clone()) * cnt.clone());
        builder.assert_zero((cnt.clone() - f(N_DBL)) * col(COL_INV10) - (one.clone() - is10.clone()));
        builder.assert_zero(is10.clone() * (cnt.clone() - f(N_DBL)));
        let gh = cont.clone() * kh.clone();
        builder.assert_zero(gh.clone() * (one.clone() - is10.clone()) * (nx[COL_CNT].clone() - cnt.clone() - one.clone()));
        builder.assert_zero(gh.clone() * is10.clone() * nx[COL_CNT].clone());
        builder.assert_zero(gh.clone() * is10.clone() * (nx[COL_J].clone() - j.clone() - one.clone()));
        builder.assert_zero(gh.clone() * (one.clone() - is10.clone()) * (nx[COL_J].clone() - j.clone()));
        builder.assert_zero(start.clone() * kh.clone() * cnt.clone());
        builder.assert_zero(start.clone() * kh.clone() * (j.clone() - f(N_WINDOWS - 1)));
        builder.assert_zero(head.clone() * kh.clone() * cnt.clone());
        builder.assert_zero(head.clone() * kh.clone() * j.clone());
        builder.assert_zero((one.clone() - kh.clone()) * cnt.clone());
        // acc_in = start·(0,1) + (1−start)·next.acc_out
        let acc_x: Vec<AB::IF> = (0..32).map(|i| cont.clone() * nx[COL_X3 + i].clone()).collect();
        let acc_y: Vec<AB::IF> = (0..32).map(|i| { let v = cont.clone() * nx[COL_Y3 + i].clone(); if i == 0 { v + start.clone() } else { v } }).collect();
        for i in 0..32 { builder.assert_zero(dbl.clone() * (px[i].clone() - acc_x[i].clone())); builder.assert_zero(dbl.clone() * (py[i].clone() - acc_y[i].clone())); }

        // ---- bucket rows: the point from memory ----
        builder.assert_zero(kb.clone() * (col(COL_PXPTR) - col(COL_PTR) - sgn.clone() * f(POINT_NX_OFFSET)));
        builder.assert_zero(kb.clone() * (col(COL_PYPTR) - col(COL_PTR) - f(32)));
        for i in 0..32 { builder.assert_zero(kb.clone() * (px[i].clone() - c[COL_PX_MEM + i].clone())); builder.assert_zero(kb.clone() * (py[i].clone() - c[COL_PY_MEM + i].clone())); }
        // ---- empty red1 rows add the neutral element ----
        for i in 0..32 { builder.assert_zero(empty.clone() * px[i].clone()); builder.assert_zero(empty.clone() * (py[i].clone() - if i == 0 { one.clone() } else { AB::IF::ZERO })); }

        // ---- the six identities (gated by active) ----
        let d: Vec<AB::IF> = D_LIMBS.iter().map(|&v| AB::IF::from_usize(v as usize)).collect();
        let hr = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };
        let hz = |base: usize| -> HintCols<'_, AB::IF> { HintCols { r: None, q: &c[base..base + QL], w: &c[base + QL..base + QL + WL] } };
        let g = active.clone();
        let (t1, h1) = hr(COL_T1); eval_identity(builder, &g, &[(&acc_x, &px, true)], &[], &h1, &P_25519);
        let (t2, h2) = hr(COL_T2); eval_identity(builder, &g, &[(&acc_y, &py, true)], &[], &h2, &P_25519);
        let (fv, hf) = hr(COL_F); eval_identity(builder, &g, &[(&t1, &t2, true)], &[], &hf, &P_25519);
        let (gv, hg) = hr(COL_G); eval_identity(builder, &g, &[(&d, &fv, true)], &[], &hg, &P_25519);
        eval_identity(builder, &g, &[(&x3, &gv, true), (&acc_x, &py, false), (&px, &acc_y, false)], &[(&x3, true)], &hz(COL_X3H), &P_25519);
        eval_identity(builder, &g, &[(&y3, &gv, false)], &[(&y3, true), (&t2, false), (&t1, false)], &hz(COL_Y3H), &P_25519);
        // ---- final row (horner head): x3 ≡ 0, y3 ≡ 1 ----
        let gf = active.clone() * head.clone() * kh.clone();
        let one_limbs: Vec<AB::IF> = (0..32).map(|i| if i == 0 { one.clone() } else { AB::IF::ZERO }).collect();
        eval_identity(builder, &gf, &[], &[(&x3, true)], &hz(COL_ZX), &P_25519);
        eval_identity(builder, &gf, &[], &[(&y3, true), (&one_limbs, false)], &hz(COL_ZY), &P_25519);
    }
}
// alpha slots 2·39 + flags 11 + kinds 1 + singleton 2 + mults 9 + empty 1 + continuity 8 + b 4 + horner 77 + bucket 66 + empty rows 64 + identities 6·65 + final 2·65
pub const N_CONSTRAINTS: usize = 2 * N_COLUMN_BUSES + 11 + 1 + 2 + 9 + 1 + 8 + 4 + 77 + 66 + 64 + 6 * 65 + 2 * 65;

impl<const BUS: bool> TableT for EdAddTable<BUS> {
    fn name(&self) -> &'static str { "ed_add" }
    fn table(&self) -> Table { Table::ed_add() }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        let cb = |dir: BusDirection, mult: usize, ds: usize, data: Vec<BusData>| BusInteraction { direction: dir, multiplicity: BusMultiplicity::Column(mult), domainsep: BusData::Constant(ds), data };
        let jb = |k: usize| vec![BusData::Column(COL_J), BusData::Column(COL_B), BusData::Constant(k)];
        let jk = |k: usize| vec![BusData::Column(COL_J), BusData::Constant(k)];
        let mut buses = vec![cb(BusDirection::Pull, COL_MROUTE, LOGUP_ROUTING_DOMAINSEP, vec![BusData::Column(COL_J), BusData::Column(COL_B), BusData::Column(COL_SGN), BusData::Column(COL_PTR)])];
        for k in 0..N_CHUNKS { let mut d = jb(k); d.extend(chunk_data(COL_X3, COL_Y3, k)); buses.push(cb(BusDirection::Push, COL_MBFP, LOGUP_BUCKET_FINAL_DOMAINSEP, d)); }
        for k in 0..N_CHUNKS { let mut d = jb(k); d.extend(chunk_data(COL_PX, COL_PY, k)); buses.push(cb(BusDirection::Pull, COL_MR1PULL, LOGUP_BUCKET_FINAL_DOMAINSEP, d)); }
        for k in 0..N_CHUNKS { let mut d = jb(k); d.extend(chunk_data(COL_X3, COL_Y3, k)); buses.push(cb(BusDirection::Push, COL_MR1, LOGUP_RED1_OUT_DOMAINSEP, d)); }
        for k in 0..N_CHUNKS { let mut d = jb(k); d.extend(chunk_data(COL_PX, COL_PY, k)); buses.push(cb(BusDirection::Pull, COL_MR2, LOGUP_RED1_OUT_DOMAINSEP, d)); }
        for k in 0..N_CHUNKS { let mut d = jk(k); d.extend(chunk_data(COL_X3, COL_Y3, k)); buses.push(cb(BusDirection::Push, COL_MTJ, LOGUP_TJ_DOMAINSEP, d)); }
        for k in 0..N_CHUNKS { let mut d = jk(k); d.extend(chunk_data(COL_PX, COL_PY, k)); buses.push(cb(BusDirection::Pull, COL_MHA, LOGUP_TJ_DOMAINSEP, d)); }
        buses.push(cb(BusDirection::Push, COL_MTOKP, LOGUP_TOKEN_DOMAINSEP, vec![BusData::Column(COL_ACTIVE)]));
        buses.push(cb(BusDirection::Pull, COL_MTOKQ, LOGUP_TOKEN_DOMAINSEP, vec![BusData::Column(COL_ACTIVE)]));
        assert_eq!(buses.len(), N_COLUMN_BUSES);
        buses.extend(memory_lookups_consecutive(COL_PXPTR, COL_PX_MEM, 32));
        buses.extend(memory_lookups_consecutive(COL_PYPTR, COL_PY_MEM, 32));
        for (section, cols) in range_cols() { buses.extend(range_lookups(&cols, section)); }
        buses
    }
    fn padding_row(&self, zero_vec_ptr: usize, _null_hash_ptr: usize, _ending_pc: usize) -> Vec<F> {
        let mut row = vec![F::ZERO; N_COLS];
        row[COL_START] = F::ONE; row[COL_HEAD] = F::ONE;
        row[COL_PXPTR] = F::from_usize(zero_vec_ptr); row[COL_PYPTR] = F::from_usize(zero_vec_ptr);
        row[COL_INV10] = (F::ZERO - F::from_usize(N_DBL)).inverse(); // cnt = 0: (0 − 10)·inv10 = 1 − is10 = 1
        row
    }
    #[inline(always)]
    fn execute<M: crate::execution::memory::MemoryAccess>(&self, _a: F, _b: F, _c: F, _args: PrecompileCompTimeArgs<usize>, _ctx: &mut InstructionContext<'_, M>) -> Result<(), RunnerError> {
        unreachable!("ed_add has no precompile: its trace is a post-pass (fill_trace_ed_add)")
    }
}

/// Range classes: x3/y3 (free outputs), identity r/q limbs bytes, witness limbs u16, cnt U4. px/py
/// are transported by memory lookups or buses from range-checked sources.
pub fn range_cols() -> Vec<(usize, Vec<usize>)> {
    let mut u8s: Vec<usize> = (COL_X3..COL_X3 + 64).collect(); let mut u16s: Vec<usize> = vec![];
    for b in [COL_T1, COL_T2, COL_F, COL_G] { u8s.extend(b..b + 32 + QL); u16s.extend(b + 66..b + 66 + WL); }
    for b in [COL_X3H, COL_Y3H, COL_ZX, COL_ZY] { u8s.extend(b..b + QL); u16s.extend(b + QL..b + QL + WL); }
    vec![(RANGE_U8, u8s), (RANGE_U16, u16s), (RANGE_U4, vec![COL_CNT])]
}

// ---------------------------------------------------------------------------------------------- trace
#[derive(Clone, Copy)]
enum Kind { Bucket, Red1, Red2, Horner }

struct Step { kind: Kind, j: usize, b: usize, sgn: u8, ptr: usize, empty: bool, cnt: usize, p: Affine }

/// One chain (forward order); returns its rows in REVERSE order (head first) and the total.
fn chain_rows(steps: &[Step], zero_ptr: usize, is_final: bool) -> (Vec<[F; N_COLS]>, Affine) {
    let fu = |b: u8| F::from_usize(b as usize);
    let m = &P_25519;
    let mut acc = NEUTRAL; let mut rows = vec![];
    let n = steps.len();
    for (k, st) in steps.iter().enumerate() {
        let acc_in = acc; let out = affine_add(&acc_in, &st.p);
        let t1 = mod_mul(&acc_in.x, &st.p.x, m); let t2 = mod_mul(&acc_in.y, &st.p.y, m); let fv = mod_mul(&t1, &t2, m); let gv = mod_mul(&D_LIMBS, &fv, m);
        let w_t1 = make_identity(&[(&acc_in.x, &st.p.x, true)], &[], false, m);
        let w_t2 = make_identity(&[(&acc_in.y, &st.p.y, true)], &[], false, m);
        let w_f = make_identity(&[(&t1, &t2, true)], &[], false, m);
        let w_g = make_identity(&[(&D_LIMBS, &fv, true)], &[], false, m);
        let w_x = make_identity(&[(&out.x, &gv, true), (&acc_in.x, &st.p.y, false), (&st.p.x, &acc_in.y, false)], &[(&out.x, true)], true, m);
        let w_y = make_identity(&[(&out.y, &gv, false)], &[(&out.y, true), (&t2, false), (&t1, false)], true, m);
        let mut row = [F::ZERO; N_COLS];
        for i in 0..32 { row[COL_X3 + i] = fu(out.x[i]); row[COL_Y3 + i] = fu(out.y[i]); row[COL_PX + i] = fu(st.p.x[i]); row[COL_PY + i] = fu(st.p.y[i]); }
        let put_r = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
        let put_z = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..QL { row[base + i] = fu(w.q[i]); } for i in 0..WL { row[base + QL + i] = F::from_usize(w.w[i] as usize); } };
        put_r(&mut row, COL_T1, &w_t1); put_r(&mut row, COL_T2, &w_t2); put_r(&mut row, COL_F, &w_f); put_r(&mut row, COL_G, &w_g);
        put_z(&mut row, COL_X3H, &w_x); put_z(&mut row, COL_Y3H, &w_y);
        let is_start = k == 0; let is_head = k == n - 1;
        row[COL_START] = F::from_bool(is_start); row[COL_HEAD] = F::from_bool(is_head); row[COL_ACTIVE] = F::ONE;
        row[COL_J] = F::from_usize(st.j); row[COL_B] = F::from_usize(st.b); row[COL_SGN] = fu(st.sgn); row[COL_EMPTY] = F::from_bool(st.empty);
        let (kb, kr1, kr2, kh) = match st.kind { Kind::Bucket => (1, 0, 0, 0), Kind::Red1 => (0, 1, 0, 0), Kind::Red2 => (0, 0, 1, 0), Kind::Horner => (0, 0, 0, 1) };
        row[COL_KB] = F::from_usize(kb); row[COL_KR1] = F::from_usize(kr1); row[COL_KR2] = F::from_usize(kr2); row[COL_KH] = F::from_usize(kh);
        row[COL_CNT] = F::from_usize(st.cnt);
        let dbl = st.cnt != 0; row[COL_DBL] = F::from_bool(dbl);
        row[COL_INV0] = if dbl { F::from_usize(st.cnt).inverse() } else { F::ZERO };
        let is10 = st.cnt == N_DBL; row[COL_IS10] = F::from_bool(is10);
        row[COL_INV10] = if is10 { F::ZERO } else { (F::from_usize(st.cnt) - F::from_usize(N_DBL)).inverse() };
        if matches!(st.kind, Kind::Bucket) {
            row[COL_PTR] = F::from_usize(st.ptr);
            row[COL_PXPTR] = F::from_usize(st.ptr + st.sgn as usize * POINT_NX_OFFSET); row[COL_PYPTR] = F::from_usize(st.ptr + 32);
            for i in 0..32 { row[COL_PX_MEM + i] = fu(st.p.x[i]); row[COL_PY_MEM + i] = fu(st.p.y[i]); }
        } else { row[COL_PXPTR] = F::from_usize(zero_ptr); row[COL_PYPTR] = F::from_usize(zero_ptr); }
        let (fb, fh) = (F::from_bool(is_start), F::from_bool(is_head));
        row[COL_MROUTE] = F::from_usize(kb); row[COL_MBFP] = F::from_usize(kb) * fh; row[COL_MR1PULL] = F::from_usize(kr1) * F::from_bool(!st.empty);
        row[COL_MR1] = F::from_usize(kr1); row[COL_MR2] = F::from_usize(kr2); row[COL_MTJ] = F::from_usize(kr2) * fh; row[COL_MHA] = F::from_usize(kh) * F::from_bool(!dbl);
        row[COL_MTOKP] = fb; row[COL_MTOKQ] = fh;
        if is_head && is_final {
            let one = NEUTRAL.y;
            // zero-checks hold only for a valid batch; otherwise leave zeros and let the AIR reject
            if out == NEUTRAL {
                put_z(&mut row, COL_ZX, &make_identity(&[], &[(&out.x, true)], true, m));
                put_z(&mut row, COL_ZY, &make_identity(&[], &[(&out.y, true), (&one, false)], true, m));
            }
        }
        rows.push(row); acc = out;
    }
    rows.reverse();
    (rows, acc)
}

/// Post-pass: build the whole EdAdd trace from the routing tuples of ScalarL/SignerScalar and the
/// point records in memory. Returns the MSM total (O for a valid batch).
pub fn fill_trace_ed_add(traces: &mut BTreeMap<Table, TableTrace>, memory: &[F], zero_ptr: usize) -> Affine {
    use crate::tables::ed25519::{scalar_table as t4, signer_scalar_table as t7};
    let cell = |c: &ArenaVec<F>, r: usize| c[r].as_canonical_u32() as usize;
    let mut tuples: Vec<(usize, usize, u8, usize)> = vec![];
    if let Some(tr) = traces.get(&Table::scalar_l()) {
        for r in 0..tr.columns[t4::COL_MULT].len() {
            if cell(&tr.columns[t4::COL_MULT], r) != 1 { continue; }
            for j in 0..t4::WINDOWS { if cell(&tr.columns[t4::COL_NZ + j], r) == 1 { tuples.push((j, cell(&tr.columns[t4::COL_M + j], r), cell(&tr.columns[t4::COL_NSGN + j], r) as u8, cell(&tr.columns[t4::COL_PTR], r))); } }
        }
    }
    if let Some(tr) = traces.get(&Table::signer_scalar()) {
        for r in 0..tr.columns[t7::COL_MULT].len() {
            if cell(&tr.columns[t7::COL_MULT], r) != 1 { continue; }
            for j in 0..t7::T7_WINDOWS { if cell(&tr.columns[t7::COL_NZ + j], r) == 1 { tuples.push((j, cell(&tr.columns[t7::COL_M + j], r), cell(&tr.columns[t7::COL_PSGN + j], r) as u8, cell(&tr.columns[t7::COL_PTR], r))); } }
        }
    }
    // No routing tuples (a program with no ed25519 precompile calls, e.g. every node proof): the table
    // is padding only. The padding row is a valid inactive singleton and the token bus balances 0 = 0,
    // so nothing needs a chain. (Building the 26,900-row reduction structure here used to cost every
    // proof a 2^15-row, 1,132-column table.)
    if tuples.is_empty() { return NEUTRAL; }
    let point = |ptr: usize, sgn: u8| -> Affine {
        let byte = |i: usize| -> u8 { let v = memory[i].as_canonical_u32(); assert!(v < 256, "ed_add: point cell is not a byte"); v as u8 };
        let xo = ptr + sgn as usize * POINT_NX_OFFSET;
        Affine { x: std::array::from_fn(|i| byte(xo + i)), y: std::array::from_fn(|i| byte(ptr + 32 + i)) }
    };
    let mut buckets: BTreeMap<(usize, usize), Vec<Step>> = BTreeMap::new();
    for (j, b, sgn, ptr) in tuples { assert!(b >= 1 && b <= N_BUCKETS && j < N_WINDOWS, "ed_add: routing tuple out of range"); buckets.entry((j, b)).or_default().push(Step { kind: Kind::Bucket, j, b, sgn, ptr, empty: false, cnt: 0, p: point(ptr, sgn) }); }
    let mut rows: Vec<[F; N_COLS]> = vec![];
    let mut totals: BTreeMap<(usize, usize), Affine> = BTreeMap::new();
    for ((j, b), steps) in &buckets { let (r, total) = chain_rows(steps, zero_ptr, false); rows.extend(r); totals.insert((*j, *b), total); }
    let mut tj: Vec<Affine> = vec![];
    for j in 0..N_WINDOWS {
        let mut red1 = vec![]; let mut sb = vec![];
        let mut s = NEUTRAL;
        for b in (1..=N_BUCKETS).rev() { let p = totals.get(&(j, b)).copied(); red1.push(Step { kind: Kind::Red1, j, b, sgn: 0, ptr: 0, empty: p.is_none(), cnt: 0, p: p.unwrap_or(NEUTRAL) }); s = affine_add(&s, &p.unwrap_or(NEUTRAL)); sb.push(s); }
        let (r, _) = chain_rows(&red1, zero_ptr, false); rows.extend(r);
        let red2: Vec<Step> = (1..=N_BUCKETS).rev().enumerate().map(|(i, b)| Step { kind: Kind::Red2, j, b, sgn: 0, ptr: 0, empty: false, cnt: 0, p: sb[i] }).collect();
        let (r, t) = chain_rows(&red2, zero_ptr, false); rows.extend(r); tj.push(t);
    }
    let mut horner = vec![Step { kind: Kind::Horner, j: N_WINDOWS - 1, b: 0, sgn: 0, ptr: 0, empty: false, cnt: 0, p: tj[N_WINDOWS - 1] }];
    let mut acc = tj[N_WINDOWS - 1];
    for j in (0..N_WINDOWS - 1).rev() {
        for cnt in (1..=N_DBL).rev() { horner.push(Step { kind: Kind::Horner, j, b: 0, sgn: 0, ptr: 0, empty: false, cnt, p: acc }); acc = affine_add(&acc, &acc); }
        horner.push(Step { kind: Kind::Horner, j, b: 0, sgn: 0, ptr: 0, empty: false, cnt: 0, p: tj[j] }); acc = affine_add(&acc, &tj[j]);
    }
    let (r, total) = chain_rows(&horner, zero_ptr, true); rows.extend(r);
    let Some(trace) = traces.get_mut(&Table::ed_add()) else { return total; };
    for row in &rows { for (i, v) in row.iter().enumerate() { trace.columns[i].push(*v); } }
    total
}
