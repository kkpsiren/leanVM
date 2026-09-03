//! Standalone prove/verify of one AIR (bus-less) in leanVM's session/WHIR setup, with shift statements.
use std::time::Instant;
use backend::*;
use lean_vm::{EF, ExtraDataForBuses, F};
use sub_protocols::{AirSumcheckSession, OuterSumcheckSession, compute_shifted_columns, natural_ordering_point_for_session, prove_batched_air_sumcheck};

#[derive(Debug, Clone)]
pub struct Stats { pub prove_secs: f64, pub commit_secs: f64, pub air_secs: f64, pub open_secs: f64, pub verify_secs: f64, pub proof_fe: usize, pub cells: usize }

/// Prove and verify `air` over column-major `cols` (n_rows = cols[0].len(), a power of two).
/// Panics with "AIR constraint check failed" if the verifier's AIR check fails.
pub fn prove_verify<A: Air<ExtraData = ExtraDataForBuses<EF>> + Copy + std::fmt::Debug + 'static>(air: A, cols: Vec<Vec<F>>, rate: usize, label: &str) -> Stats {
    let n_rows = cols[0].len(); let log_n_rows = log2_strict_usize(n_rows);
    let n_cols = air.n_columns(); let n_shift = air.n_shift_columns(); let n_constraints = air.n_constraints(); let air_degree = air.degree_air();
    assert_eq!(cols.len(), n_cols);
    let whir_config_builder = WhirConfigBuilder { folding_factor: FoldingFactor::new(7, 4), soundness_type: SecurityAssumption::JohnsonBound, pow_bits: 16, max_num_variables_to_send_coeffs: 9, rs_domain_initial_reduction_factor: 5, security_level: 124, starting_log_inv_rate: rate };
    let packed_n_vars = log2_ceil_usize(n_cols << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config_builder, packed_n_vars);
    println!("[{label}] cols={n_cols} (+{n_shift} shift) rows=2^{log_n_rows} cells={} (2^{packed_n_vars}) degree={air_degree} constraints={n_constraints} rate=1/{}", n_cols << log_n_rows, 1 << rate);
    let mut prover_state = ProverState::<EF, _>::new(get_poseidon16().clone(), Default::default());
    let time = Instant::now();
    let trace: Vec<ArenaVec<F>> = cols.into_iter().map(|c| ArenaVec::from_iter(c.into_iter())).collect();
    let mut stacked = ArenaVec::filled(F::ZERO, (n_cols << log_n_rows).next_power_of_two());
    for (i, col) in trace.iter().enumerate() { stacked[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col); }
    let committed = MleOwned::Base(stacked);
    let witness = whir_config.commit(&mut prover_state, &committed, n_cols << log_n_rows);
    let commit_secs = time.elapsed().as_secs_f64();
    let alpha = prover_state.sample();
    let extra_data = ExtraDataForBuses::new(&[], alpha.powers().collect_n(n_constraints));
    prover_state.duplex();
    let eq_factor: Vec<EF> = prover_state.sample_vec(log_n_rows);
    let column_refs: Vec<&[F]> = trace.iter().map(|c| c.as_slice()).collect();
    let shifted = compute_shifted_columns(n_shift, &column_refs);
    let mut flat_and_shift: Vec<&[F]> = column_refs.clone(); flat_and_shift.extend(shifted.iter().map(|c| c.as_slice()));
    let packed = MleGroupRef::<EF>::Base(flat_and_shift).pack();
    let t_air = Instant::now();
    let mut sessions: Vec<Box<dyn OuterSumcheckSession<EF> + '_>> = vec![Box::new(AirSumcheckSession::new(packed, eq_factor, EF::ZERO, air, extra_data, n_rows))];
    let sumcheck_air_point = prove_batched_air_sumcheck(&mut prover_state, &mut sessions);
    let col_evals = sessions[0].final_column_evals();
    prover_state.add_extension_scalars(&col_evals);
    let air_secs = t_air.elapsed().as_secs_f64();
    let t_open = Instant::now();
    let point = MultilinearPoint(natural_ordering_point_for_session(&sumcheck_air_point.0, log_n_rows));
    let mut stmts = vec![SparseStatement::new(packed_n_vars, point.clone(), (0..n_cols).map(|c| SparseValue::new(c, col_evals[c])).collect())];
    if n_shift > 0 { stmts.push(SparseStatement::new_next(packed_n_vars, point.clone(), (0..n_shift).map(|c| SparseValue::new(c, col_evals[n_cols + c])).collect())); }
    whir_config.prove(&mut prover_state, stmts, witness, &committed.by_ref());
    let open_secs = t_open.elapsed().as_secs_f64();
    let prove_secs = time.elapsed().as_secs_f64();
    let proof = prover_state.into_proof(); let proof_fe = proof.proof_size_fe();
    let cells = n_cols << log_n_rows;
    println!("[{label}] prove {prove_secs:.3}s (commit {commit_secs:.3}, air {air_secs:.3}, open {open_secs:.3}) => {:.0} rows/s, {:.2} Mcells/s, {:.1} ns/cell; proof ~{} KiB", n_rows as f64 / prove_secs, cells as f64 / prove_secs / 1e6, prove_secs * 1e9 / cells as f64, proof_fe * 4 / 1024);
    let t_verify = Instant::now();
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone(), Default::default()).unwrap();
    let parsed = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();
    let alpha = verifier_state.sample();
    let extra_data = ExtraDataForBuses::new(&[], alpha.powers().collect_n(n_constraints));
    verifier_state.duplex();
    let eq_factor_v: Vec<EF> = verifier_state.sample_vec(log_n_rows);
    let Evaluation { point: pt_v, value: claimed } = sumcheck_verify(&mut verifier_state, log_n_rows, air_degree + 1, EF::ZERO, None).unwrap();
    let col_evals_v: Vec<EF> = verifier_state.next_extension_scalars_vec(n_cols + n_shift).unwrap();
    let constraint_eval = <A as SumcheckComputation<EF>>::eval_extension(&air, &col_evals_v, &extra_data);
    let natural_v = natural_ordering_point_for_session(&pt_v.0, log_n_rows);
    let eq_val = MultilinearPoint(eq_factor_v).eq_poly_outside(&MultilinearPoint(natural_v.clone()));
    assert_eq!(eq_val * constraint_eval, claimed, "AIR constraint check failed");
    let point_v = MultilinearPoint(natural_v);
    let mut stmts_v = vec![SparseStatement::new(packed_n_vars, point_v.clone(), (0..n_cols).map(|c| SparseValue::new(c, col_evals_v[c])).collect())];
    if n_shift > 0 { stmts_v.push(SparseStatement::new_next(packed_n_vars, point_v, (0..n_shift).map(|c| SparseValue::new(c, col_evals_v[n_cols + c])).collect())); }
    whir_config.verify(&mut verifier_state, &parsed, stmts_v).unwrap();
    let verify_secs = t_verify.elapsed().as_secs_f64();
    println!("[{label}] verify {:.1} ms", verify_secs * 1e3);
    Stats { prove_secs, commit_secs, air_secs, open_secs, verify_secs, proof_fe, cells }
}
