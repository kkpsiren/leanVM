//! T4 `ScalarL` (spec §3.4), standalone: one row per signature.
//!   inputs: h (64 bytes, the SHA-512 output pulled from T2), ρ (124 bits, from the transcript),
//!           s (32 bytes, the signature scalar), signer chain flags
//!   proves: c ≡ h (mod L)            via h = h_lo + 2^256·h_hi and K256 = 2^256 mod L (constant)
//!           13 signed 10-bit windows of ρ (recoding m_j ∈ [0,512], sign s_j, borrow b_j, nz_j)
//!           k ≡ ρ·c (mod L),  σ ≡ ρ·s (mod L),  s ≤ L−1 (borrow chain)
//!           lazy accumulators (reverse chains through shift columns): K_out = K_in + k limb-wise per
//!           signer, S_out = S_in + σ per leaf; limbs stay < 2^21 for ≤ 6,250 rows per chain.
//! ρ is given as 124 boolean bit columns here (the spec's cell→window bijection is the memory-side
//! encoding; the window values are what T3 consumes). Range checks (bytes, m_j·2^6, h-limbs) are LogUp
//! fractions attached in the VM integration.

use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};
use num_bigint::BigInt;
use num_integer::Integer;

use crate::gadgets::*;

pub const RHO_BITS: usize = 124;
pub const WINDOWS: usize = 13;
/// 2^256 mod L, little-endian limbs
pub fn k256_limbs() -> [u8; 32] { let m = modulus_int(&L_25519); int_to_limbs(&(BigInt::from(1u8) << 256usize).mod_floor(&m), 32).try_into().unwrap() }

// layout — shift columns first: K_out (32), S_out (32), start_K, start_S
pub const COL_KOUT: usize = 0;
pub const COL_SOUT: usize = 32;
pub const COL_START_K: usize = 64;
pub const COL_START_S: usize = 65;
pub const N_SHIFT: usize = 66;
pub const COL_HLO: usize = 66;             // 32
pub const COL_HHI: usize = 98;             // 32
pub const COL_C: usize = 130;              // 130 (r q w)
pub const COL_RHO_BITS: usize = 260;       // 124
pub const COL_M: usize = 384;              // 13
pub const COL_SGN: usize = 397;            // 13
pub const COL_BRW: usize = 410;            // 13
pub const COL_INV: usize = 423;            // 13
pub const COL_NZ: usize = 436;             // 13
pub const COL_K: usize = 449;              // 130: k ≡ ρ·c
pub const COL_S: usize = 579;              // 32: the signature scalar s
pub const COL_SIG: usize = 611;            // 130: σ ≡ ρ·s
pub const COL_SLT: usize = 741;            // 64: (L−1) − s diff + borrows
pub const N_COLS: usize = 805;

#[derive(Debug, Clone, Copy, Default)]
pub struct ScalarAir;

impl Air for ScalarAir {
    type ExtraData = ExtraDataForBuses<EF>;
    fn degree_air(&self) -> usize { 3 }
    fn n_columns(&self) -> usize { N_COLS }
    fn n_shift_columns(&self) -> usize { N_SHIFT }
    fn n_constraints(&self) -> usize { N_CONSTRAINTS }
    fn eval<AB: AirBuilder>(&self, builder: &mut AB, _extra: &Self::ExtraData) {
        let c: Vec<AB::IF> = builder.flat().to_vec();
        let nx: Vec<AB::IF> = builder.shift().to_vec();
        let one = AB::IF::ONE;
        let f = |x: usize| AB::F::from_usize(x);
        let sl = |base: usize, n: usize| -> Vec<AB::IF> { c[base..base + n].to_vec() };
        let hints_r = |base: usize| -> (Vec<AB::IF>, HintCols<'_, AB::IF>) { (c[base..base + 32].to_vec(), HintCols { r: Some(&c[base..base + 32]), q: &c[base + 32..base + 32 + QL], w: &c[base + 66..base + 66 + WL] }) };
        let k256: Vec<AB::IF> = k256_limbs().iter().map(|&b| AB::IF::from_usize(b as usize)).collect();
        // 1. c ≡ h_lo + h_hi·K256 (mod L)
        let (hlo, hhi) = (sl(COL_HLO, 32), sl(COL_HHI, 32));
        let (cv, hc) = hints_r(COL_C);
        eval_identity(builder, &one, &[(&hhi, &k256, true)], &[(&hlo, true)], &hc, &L_25519);
        // 2. ρ bits boolean; windows w_j = Σ_{t<10} bit_{10j+t}·2^t  (window 12 has 4 bits)
        let bits = sl(COL_RHO_BITS, RHO_BITS);
        for b in &bits { builder.assert_bool(b.clone()); }
        let mut rho_limbs: Vec<AB::IF> = (0..32).map(|_| AB::IF::ZERO).collect();
        for (i, b) in bits.iter().enumerate() { rho_limbs[i / 8] += b.clone() * f(1 << (i % 8)); }
        let window = |j: usize| -> AB::IF { let mut acc = AB::IF::ZERO; for t in 0..10 { let i = 10 * j + t; if i < RHO_BITS { acc += bits[i].clone() * f(1 << t); } } acc };
        // 3. signed recoding: w_j + b_{j−1} = (1 − 2s_j)·m_j + 1024·b_j ; s,b boolean; nz_j = [m_j ≠ 0]; b_12 = 0
        for j in 0..WINDOWS {
            let (m, s, b, inv, nz) = (c[COL_M + j].clone(), c[COL_SGN + j].clone(), c[COL_BRW + j].clone(), c[COL_INV + j].clone(), c[COL_NZ + j].clone());
            let b_prev = if j == 0 { AB::IF::ZERO } else { c[COL_BRW + j - 1].clone() };
            builder.assert_bool(s.clone()); builder.assert_bool(b.clone()); builder.assert_bool(nz.clone());
            builder.assert_zero(window(j) + b_prev - (one.clone() - s.double()) * m.clone() - b.clone() * f(1024));
            builder.assert_zero(m.clone() * inv - nz.clone());
            builder.assert_zero((one.clone() - nz) * m);
        }
        builder.assert_zero(c[COL_BRW + WINDOWS - 1].clone());
        // 4. k ≡ ρ·c, σ ≡ ρ·s (mod L)
        let (kv, hk) = hints_r(COL_K); eval_identity(builder, &one, &[(&rho_limbs, &cv, true)], &[], &hk, &L_25519);
        let s = sl(COL_S, 32);
        let (sig, hs) = hints_r(COL_SIG); eval_identity(builder, &one, &[(&rho_limbs, &s, true)], &[], &hs, &L_25519);
        // 5. s ≤ L − 1: (L−1)_i − s_i − prev = diff_i − 256·bw_i, final borrow 0
        let diff = sl(COL_SLT, 32); let bw = sl(COL_SLT + 32, 32);
        for i in 0..32 {
            let lm1 = if i == 0 { L_25519[0] as usize - 1 } else { L_25519[i] as usize };
            let prev = if i == 0 { AB::IF::ZERO } else { bw[i - 1].clone() };
            builder.assert_zero(AB::IF::from_usize(lm1) - s[i].clone() - prev - diff[i].clone() + bw[i].clone() * f(256));
            builder.assert_bool(bw[i].clone());
        }
        builder.assert_zero(bw[31].clone());
        // 6. lazy accumulators: out = in + value, in = start ? 0 : next.out
        let (start_k, start_s) = (c[COL_START_K].clone(), c[COL_START_S].clone());
        builder.assert_bool(start_k.clone()); builder.assert_bool(start_s.clone());
        for i in 0..32 {
            let k_in = (one.clone() - start_k.clone()) * nx[COL_KOUT + i].clone();
            builder.assert_zero(c[COL_KOUT + i].clone() - k_in - kv[i].clone());
            let s_in = (one.clone() - start_s.clone()) * nx[COL_SOUT + i].clone();
            builder.assert_zero(c[COL_SOUT + i].clone() - s_in - sig[i].clone());
        }
    }
}
// c 65 + bits 124 + windows 13×6 + 1 + k 65 + σ 65 + s<L 65 + acc 2 + 64
pub const N_CONSTRAINTS: usize = 65 + 124 + 13 * 6 + 1 + 65 + 65 + 65 + 2 + 64;

// ---- trace --------------------------------------------------------------------------------------
pub struct ScalarInput { pub h: [u8; 64], pub rho: u128, pub s: [u8; 32], pub start_k: bool, pub start_s: bool }

pub fn random_inputs(n: usize, seed: u64) -> Vec<ScalarInput> {
    let mut x = seed | 1; let mut nb = move || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; (x >> 24) as u8 };
    let l = modulus_int(&L_25519);
    (0..n).map(|i| {
        let mut h = [0u8; 64]; for b in h.iter_mut() { *b = nb(); }
        let mut rho = 0u128; for _ in 0..16 { rho = (rho << 8) | nb() as u128; } rho &= (1u128 << RHO_BITS) - 1;
        let mut s = [0u8; 32]; for b in s.iter_mut() { *b = nb(); } s = int_to_limbs(&limbs_to_int(&s).mod_floor(&l), 32).try_into().unwrap();
        ScalarInput { h, rho, s, start_k: i % 7 == 0, start_s: i == 0 }
    }).collect()
}

/// Rows of a leaf in REVERSE order (the whole leaf reversed once): row r's `next` (r+1) is its
/// predecessor for BOTH accumulator chains — the per-leaf S chain and the per-signer K segments,
/// which are contiguous in (signer_id, sig_id) order. Heads (chain totals) are the lowest rows.
pub fn build_rows(inputs: &[ScalarInput]) -> Vec<[F; N_COLS]> { generate_trace_core(inputs) }

/// Column-major trace padded to n_rows with zero-input start rows.
pub fn generate_trace(inputs: &[ScalarInput], n_rows: usize) -> (Vec<Vec<F>>, ()) {
    assert!(inputs.len() < n_rows);
    let rows = generate_trace_core(inputs);
    let pad = generate_trace_core(&[ScalarInput { h: [0u8; 64], rho: 0, s: [0u8; 32], start_k: true, start_s: true }])[0];
    let mut cols: Vec<Vec<F>> = (0..N_COLS).map(|_| vec![F::ZERO; n_rows]).collect();
    for (r, row) in rows.iter().enumerate() { for c in 0..N_COLS { cols[c][r] = row[c]; } }
    for r in rows.len()..n_rows { for c in 0..N_COLS { cols[c][r] = pad[c]; } }
    (cols, ())
}

fn generate_trace_core(inputs: &[ScalarInput]) -> Vec<[F; N_COLS]> {
    // (kept separate so the padding derivation cannot recurse into padding)
    let fu = |b: u8| F::from_usize(b as usize);
    let l = &L_25519; let k256 = k256_limbs();
    let mut rows: Vec<[F; N_COLS]> = vec![]; let mut per_row: Vec<([u8; 32], [u8; 32])> = vec![];
    for inp in inputs {
        let mut row = [F::ZERO; N_COLS];
        let hlo: [u8; 32] = inp.h[..32].try_into().unwrap(); let hhi: [u8; 32] = inp.h[32..].try_into().unwrap();
        for i in 0..32 { row[COL_HLO + i] = fu(hlo[i]); row[COL_HHI + i] = fu(hhi[i]); }
        let wc = make_identity(&[(&hhi, &k256, true)], &[(&hlo, true)], false, l);
        let put = |row: &mut [F; N_COLS], base: usize, w: &IdentityWitness| { for i in 0..32 { row[base + i] = fu(w.r[i]); } for i in 0..QL { row[base + 32 + i] = fu(w.q[i]); } for i in 0..WL { row[base + 66 + i] = F::from_usize(w.w[i] as usize); } };
        put(&mut row, COL_C, &wc);
        for i in 0..RHO_BITS { row[COL_RHO_BITS + i] = F::from_bool((inp.rho >> i) & 1 == 1); }
        let mut rho_limbs = [0u8; 32]; for i in 0..16 { rho_limbs[i] = ((inp.rho >> (8 * i)) & 255) as u8; }
        let mut borrow = 0i64;
        for j in 0..WINDOWS { let w = ((inp.rho >> (10 * j)) & 1023) as i64 + borrow; let (m, sgn, b) = if w > 512 { (1024 - w, 1, 1) } else { (w, 0, 0) }; borrow = b; row[COL_M + j] = F::from_usize(m as usize); row[COL_SGN + j] = fu(sgn as u8); row[COL_BRW + j] = fu(b as u8); row[COL_NZ + j] = F::from_bool(m != 0); row[COL_INV + j] = if m != 0 { F::from_usize(m as usize).inverse() } else { F::ZERO }; }
        assert_eq!(borrow, 0);
        let wk = make_identity(&[(&rho_limbs, &wc.r, true)], &[], false, l); put(&mut row, COL_K, &wk);
        for i in 0..32 { row[COL_S + i] = fu(inp.s[i]); }
        let ws = make_identity(&[(&rho_limbs, &inp.s, true)], &[], false, l); put(&mut row, COL_SIG, &ws);
        { let mut bw = 0i32; for i in 0..32 { let lm1 = if i == 0 { L_25519[0] as i32 - 1 } else { L_25519[i] as i32 }; let mut d = lm1 - inp.s[i] as i32 - bw; bw = 0; if d < 0 { d += 256; bw = 1; } row[COL_SLT + i] = fu(d as u8); row[COL_SLT + 32 + i] = fu(bw as u8); } assert_eq!(bw, 0, "s must be < L"); }
        row[COL_START_K] = F::from_bool(inp.start_k); row[COL_START_S] = F::from_bool(inp.start_s);
        per_row.push((wk.r, ws.r)); rows.push(row);
    }
    let mut kacc = [0i64; 32]; let mut sacc = [0i64; 32];
    for (idx, inp) in inputs.iter().enumerate() {
        if inp.start_k { kacc = [0; 32]; } if inp.start_s { sacc = [0; 32]; }
        for i in 0..32 { kacc[i] += per_row[idx].0[i] as i64; sacc[i] += per_row[idx].1[i] as i64; rows[idx][COL_KOUT + i] = F::from_usize(kacc[i] as usize); rows[idx][COL_SOUT + i] = F::from_usize(sacc[i] as usize); }
    }
    rows.reverse();
    rows
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
    let n_rows = cols[0].len(); let extra = ExtraDataForBuses::new(&[], vec![]);
    for r in 0..n_rows {
        let flat: Vec<F> = (0..N_COLS).map(|c| cols[c][r]).collect();
        let shift: Vec<F> = (0..N_SHIFT).map(|c| cols[c][(r + 1).min(n_rows - 1)]).collect();
        let mut b = DebugBuilder { flat: &flat, shift: &shift, idx: 0, failures: vec![] };
        ScalarAir.eval(&mut b, &extra);
        assert_eq!(b.idx, N_CONSTRAINTS, "N_CONSTRAINTS mismatch: counted {}", b.idx);
        if let Some(&c) = b.failures.first() { return Some((r, c)); }
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::Zero;
    #[test]
    fn scalar_rows_hold_and_reduce_correctly() {
        let inputs = random_inputs(20, 3);
        let (cols, _) = generate_trace(&inputs, 32);
        assert_eq!(check_trace(&cols), None);
        // c ≡ h mod L check on the first emitted row (reverse layout: emitted rows are chains reversed) — recompute for input 0
        let l = modulus_int(&L_25519);
        let rows = build_rows(&inputs[..1]);
        let c_limbs: Vec<u8> = (0..32).map(|i| rows[0][COL_C + i].as_canonical_u32() as u8).collect();
        assert_eq!(limbs_to_int(&c_limbs), limbs_to_int(&inputs[0].h).mod_floor(&l));
        // windows reconstruct ρ: Σ (1−2s)·m·2^{10j} = ρ
        let mut acc = BigInt::zero();
        for j in 0..WINDOWS { let m = rows[0][COL_M + j].as_canonical_u32() as i64; let s = rows[0][COL_SGN + j].as_canonical_u32() as i64; acc += BigInt::from((1 - 2 * s) * m) << (10 * j); }
        assert_eq!(acc, BigInt::from(inputs[0].rho));
        // tamper a ρ bit, a scalar limb, an accumulator limb
        let (mut t, _) = generate_trace(&inputs, 32); t[COL_RHO_BITS + 3][2] = F::ONE - t[COL_RHO_BITS + 3][2]; assert!(check_trace(&t).is_some());
        let (mut t, _) = generate_trace(&inputs, 32); t[COL_S + 1][4] += F::ONE; assert!(check_trace(&t).is_some());
        let (mut t, _) = generate_trace(&inputs, 32); t[COL_KOUT + 5][1] += F::ONE; assert!(check_trace(&t).is_some());
    }
}
