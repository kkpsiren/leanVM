//! Standalone prove/verify + throughput of the EdAdd (T3) AIR.
//! LOG_N_ROWS=14 RATE=1 cargo test --release -p ed_air --test prove_edadd -- test_prove_edadd --exact --nocapture
use std::time::Instant;
use backend::*;
use ed_air::edadd::{Chain, EdAddAir, N_COLS, N_SHIFT, check_trace, generate_trace, random_points};
use lean_vm::{EF, ExtraDataForBuses, F};
use sub_protocols::{AirSumcheckSession, OuterSumcheckSession, compute_shifted_columns, natural_ordering_point_for_session, prove_batched_air_sumcheck};
fn env_usize(name: &str, default: usize) -> usize { std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default) }

fn run(log_n_rows: usize, rate: usize, corrupt: bool) {
    let n_rows = 1 << log_n_rows;
    let t0 = Instant::now();
    let pts = random_points(n_rows - 1, 11);
    let chains: Vec<Chain> = pts.chunks(512).map(|c| Chain { points: c.to_vec() }).collect();
    let (mut cols, _) = generate_trace(&chains, n_rows);
    if corrupt { cols[ed_air::edadd::COL_X3 + 4][2] += F::ONE; } else { assert_eq!(check_trace(&cols), None); }
    let wit_secs = t0.elapsed().as_secs_f64();
    let air = EdAddAir; let n_cols = N_COLS; let n_constraints = air.n_constraints(); let air_degree = air.degree_air();
    println!("config: adds={} cols={n_cols} (+{N_SHIFT} shift) rows=2^{log_n_rows} cells={} (2^{}) degree={air_degree} constraints={n_constraints} rate=1/{} witness_gen={wit_secs:.2}s", n_rows - 1, n_cols << log_n_rows, log2_ceil_usize(n_cols << log_n_rows), 1 << rate);
    let whir_config_builder = WhirConfigBuilder { folding_factor: FoldingFactor::new(7, 4), soundness_type: SecurityAssumption::JohnsonBound, pow_bits: 16, max_num_variables_to_send_coeffs: 9, rs_domain_initial_reduction_factor: 5, security_level: 124, starting_log_inv_rate: rate };
    let packed_n_vars = log2_ceil_usize(n_cols << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config_builder, packed_n_vars);
    let mut prover_state = ProverState::<EF, _>::new(get_poseidon16().clone(), Default::default());
    let time = Instant::now();
    let trace: Vec<ArenaVec<F>> = cols.into_iter().map(|c| ArenaVec::from_iter(c.into_iter())).collect();
    let mut stacked = ArenaVec::filled(F::ZERO, (n_cols << log_n_rows).next_power_of_two());
    for (i, col) in trace.iter().enumerate() { stacked[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col); }
    let committed = MleOwned::Base(stacked);
    let witness = whir_config.commit(&mut prover_state, &committed, n_cols << log_n_rows);
    let t_commit = time.elapsed().as_secs_f64();
    let alpha = prover_state.sample();
    let extra_data = ExtraDataForBuses::new(&[], alpha.powers().collect_n(n_constraints));
    prover_state.duplex();
    let eq_factor: Vec<EF> = prover_state.sample_vec(log_n_rows);
    let column_refs: Vec<&[F]> = trace.iter().map(|c| c.as_slice()).collect();
    let shifted = compute_shifted_columns(N_SHIFT, &column_refs);
    let mut flat_and_shift: Vec<&[F]> = column_refs.clone(); flat_and_shift.extend(shifted.iter().map(|c| c.as_slice()));
    let packed = MleGroupRef::<EF>::Base(flat_and_shift).pack();
    let t_air = Instant::now();
    let mut sessions: Vec<Box<dyn OuterSumcheckSession<EF> + '_>> = vec![Box::new(AirSumcheckSession::new(packed, eq_factor, EF::ZERO, air, extra_data, n_rows))];
    let sumcheck_air_point = prove_batched_air_sumcheck(&mut prover_state, &mut sessions);
    let col_evals = sessions[0].final_column_evals();
    prover_state.add_extension_scalars(&col_evals);
    let t_air = t_air.elapsed().as_secs_f64();
    let t_open = Instant::now();
    let point = MultilinearPoint(natural_ordering_point_for_session(&sumcheck_air_point.0, log_n_rows));
    let flat_stmt = SparseStatement::new(packed_n_vars, point.clone(), (0..n_cols).map(|c| SparseValue::new(c, col_evals[c])).collect());
    let next_stmt = SparseStatement::new_next(packed_n_vars, point.clone(), (0..N_SHIFT).map(|c| SparseValue::new(c, col_evals[n_cols + c])).collect());
    whir_config.prove(&mut prover_state, vec![flat_stmt, next_stmt], witness, &committed.by_ref());
    let t_open = t_open.elapsed().as_secs_f64();
    let prove_secs = time.elapsed().as_secs_f64();
    let proof = prover_state.into_proof(); let proof_len = proof.proof_size_fe();
    let cells = (n_cols << log_n_rows) as f64;
    println!("prove: {prove_secs:.3}s total (commit {t_commit:.3}s, air-sumcheck {t_air:.3}s, whir-open {t_open:.3}s) => {:.0} adds/s, {:.2} Mcells/s, {:.1} ns/cell; proof {proof_len} fe (~{} KiB)", n_rows as f64 / prove_secs, cells / prove_secs / 1e6, prove_secs * 1e9 / cells, proof_len * 4 / 1024);
    let t_verify = Instant::now();
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone(), Default::default()).unwrap();
    let parsed = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();
    let alpha = verifier_state.sample();
    let extra_data = ExtraDataForBuses::new(&[], alpha.powers().collect_n(n_constraints));
    verifier_state.duplex();
    let eq_factor_v: Vec<EF> = verifier_state.sample_vec(log_n_rows);
    let Evaluation { point: pt_v, value: claimed } = sumcheck_verify(&mut verifier_state, log_n_rows, air_degree + 1, EF::ZERO, None).unwrap();
    let col_evals_v: Vec<EF> = verifier_state.next_extension_scalars_vec(n_cols + N_SHIFT).unwrap();
    let constraint_eval = <EdAddAir as SumcheckComputation<EF>>::eval_extension(&air, &col_evals_v, &extra_data);
    let natural_v = natural_ordering_point_for_session(&pt_v.0, log_n_rows);
    let eq_val = MultilinearPoint(eq_factor_v).eq_poly_outside(&MultilinearPoint(natural_v.clone()));
    assert_eq!(eq_val * constraint_eval, claimed, "AIR constraint check failed");
    let point_v = MultilinearPoint(natural_v);
    let flat_v = SparseStatement::new(packed_n_vars, point_v.clone(), (0..n_cols).map(|c| SparseValue::new(c, col_evals_v[c])).collect());
    let next_v = SparseStatement::new_next(packed_n_vars, point_v, (0..N_SHIFT).map(|c| SparseValue::new(c, col_evals_v[n_cols + c])).collect());
    whir_config.verify(&mut verifier_state, &parsed, vec![flat_v, next_v]).unwrap();
    println!("verify: {:.1} ms", t_verify.elapsed().as_secs_f64() * 1e3);
}
#[test] fn test_prove_edadd() { run(env_usize("LOG_N_ROWS", 9), env_usize("RATE", 1), false); }
#[test] #[should_panic(expected = "AIR constraint check failed")] fn test_reject_corrupted_edadd() { run(8, 1, true); }
