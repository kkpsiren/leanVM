//! Milestone 1b harness (clone of sub_protocols/tests/prove_poseidon.rs with LimbMulAir).
//!
//! LOG_N_ROWS=16 K=4 BOOST=0 RATE=2 cargo test --release -p ed_air --test prove_ed_air -- test_prove_limb_mul --exact --nocapture

use std::time::Instant;

use backend::*;
use ed_air::{LimbMulAir, generate_trace};
use lean_vm::{EF, ExtraDataForBuses, F};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{
    AirSumcheckSession, OuterSumcheckSession, natural_ordering_point_for_session, prove_batched_air_sumcheck,
};

fn env_usize(name: &str, default: usize) -> usize {
    std::env::var(name).ok().and_then(|v| v.parse().ok()).unwrap_or(default)
}

/// Runs prove + verify; returns (prove_secs, verify_secs, proof_len_elems).
fn run(air: LimbMulAir, log_n_rows: usize, rate: usize, corrupt: bool) -> (f64, f64, usize) {
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);
    let n_cols = air.n_columns();

    let t_wit = Instant::now();
    let mut cols = generate_trace(&air, n_rows, || rng.random::<u8>());
    if corrupt {
        // flip one result limb in row 3 of check 0
        let lay = air.layout();
        cols[lay.r + 5][3] += F::ONE;
    }
    let trace: Vec<ArenaVec<F>> = cols.into_iter().map(|c| ArenaVec::from_iter(c.into_iter())).collect();
    let wit_secs = t_wit.elapsed().as_secs_f64();

    let n_constraints = air.n_constraints();
    let air_degree = air.degree_air();

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 9,
        rs_domain_initial_reduction_factor: 5,
        security_level: 124,
        starting_log_inv_rate: rate,
    };

    let packed_n_vars = log2_ceil_usize(n_cols << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config_builder, packed_n_vars);

    println!(
        "config: k={} boost={} cols={} rows=2^{} cells={} (2^{}) degree={} constraints={} rate=1/{} witness_gen={:.2}s",
        air.k,
        air.boost,
        n_cols,
        log_n_rows,
        n_cols << log_n_rows,
        packed_n_vars,
        air_degree,
        n_constraints,
        1 << rate,
        wit_secs
    );

    let mut prover_state = ProverState::<EF, _>::new(get_poseidon16().clone(), Default::default());

    let time = Instant::now();

    let mut commitmed_pol = ArenaVec::filled(F::ZERO, (n_cols << log_n_rows).next_power_of_two());
    for (i, col) in trace.iter().enumerate() {
        commitmed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
    }
    let committed_pol = MleOwned::Base(commitmed_pol);
    let witness = whir_config.commit(&mut prover_state, &committed_pol, n_cols << log_n_rows);
    let t_commit = time.elapsed().as_secs_f64();

    let alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(n_constraints);
    let extra_data = ExtraDataForBuses::new(&[], air_alpha_powers);
    prover_state.duplex();
    let eq_factor: Vec<EF> = prover_state.sample_vec(log_n_rows);
    let column_refs: Vec<&[F]> = trace.iter().map(|c| c.as_slice()).collect();
    let packed = MleGroupRef::<EF>::Base(column_refs).pack();

    let t_air = Instant::now();
    let mut sessions: Vec<Box<dyn OuterSumcheckSession<EF> + '_>> = vec![Box::new(AirSumcheckSession::new(
        packed,
        eq_factor,
        EF::ZERO,
        air,
        extra_data,
        n_rows,
    ))];

    let sumcheck_air_point = prove_batched_air_sumcheck(&mut prover_state, &mut sessions);
    let col_evals = sessions[0].final_column_evals();
    prover_state.add_extension_scalars(&col_evals);
    let t_air = t_air.elapsed().as_secs_f64();

    let t_open = Instant::now();
    let natural_ordering_point = natural_ordering_point_for_session(&sumcheck_air_point.0, log_n_rows);
    let betas: Vec<EF> = prover_state.sample_vec(log2_ceil_usize(n_cols));
    let packed_point = MultilinearPoint([betas.clone(), natural_ordering_point].concat());
    let packed_eval = padd_with_zero_to_next_power_of_two(&col_evals).evaluate(&MultilinearPoint(betas));

    whir_config.prove(
        &mut prover_state,
        vec![SparseStatement::dense(packed_point, packed_eval)],
        witness,
        &committed_pol.by_ref(),
    );
    let t_open = t_open.elapsed().as_secs_f64();
    let prove_secs = time.elapsed().as_secs_f64();

    let proof = prover_state.into_proof();
    let proof_len = proof.proof_size_fe();

    let cells = (n_cols << log_n_rows) as f64;
    println!(
        "prove: {:.3}s total (commit {:.3}s, air-sumcheck {:.3}s, whir-open {:.3}s) => {:.0} rows/s, {:.2} Mcells/s, {:.1} ns/cell; proof {} field elems (~{} KiB)",
        prove_secs,
        t_commit,
        t_air,
        t_open,
        n_rows as f64 / prove_secs,
        cells / prove_secs / 1e6,
        prove_secs * 1e9 / cells,
        proof_len,
        proof_len * 4 / 1024
    );

    let t_verify = Instant::now();
    let mut verifier_state = VerifierState::<EF, _>::new(proof, get_poseidon16().clone(), Default::default()).unwrap();

    let parsed_commitment = whir_config.parse_commitment::<F>(&mut verifier_state).unwrap();

    let alpha = verifier_state.sample();
    let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(n_constraints);
    let extra_data = ExtraDataForBuses::new(&[], air_alpha_powers);

    verifier_state.duplex();
    let eq_factor_v: Vec<EF> = verifier_state.sample_vec(log_n_rows);

    let Evaluation {
        point: sumcheck_air_point_v,
        value: claimed_air_final_value,
    } = sumcheck_verify(&mut verifier_state, log_n_rows, air_degree + 1, EF::ZERO, None).unwrap();

    let col_evals_v: Vec<EF> = verifier_state.next_extension_scalars_vec(n_cols).unwrap();
    let constraint_eval = <LimbMulAir as SumcheckComputation<EF>>::eval_extension(&air, &col_evals_v, &extra_data);

    let natural_ordering_point_v = natural_ordering_point_for_session(&sumcheck_air_point_v.0, log_n_rows);
    let eq_val = MultilinearPoint(eq_factor_v).eq_poly_outside(&MultilinearPoint(natural_ordering_point_v.clone()));
    assert_eq!(eq_val * constraint_eval, claimed_air_final_value, "AIR constraint check failed");

    let betas_v: Vec<EF> = verifier_state.sample_vec(log2_ceil_usize(n_cols));
    let packed_point_v = MultilinearPoint([betas_v.clone(), natural_ordering_point_v].concat());
    let packed_eval_v = padd_with_zero_to_next_power_of_two(&col_evals_v).evaluate(&MultilinearPoint(betas_v));

    whir_config
        .verify(
            &mut verifier_state,
            &parsed_commitment,
            vec![SparseStatement::dense(packed_point_v, packed_eval_v)],
        )
        .unwrap();
    let verify_secs = t_verify.elapsed().as_secs_f64();
    println!("verify: {:.1} ms", verify_secs * 1e3);
    (prove_secs, verify_secs, proof_len)
}

#[test]
fn test_prove_limb_mul() {
    let log_n_rows = env_usize("LOG_N_ROWS", 10);
    let k = env_usize("K", 4);
    let boost = env_usize("BOOST", 0) == 1;
    let rate = env_usize("RATE", 1);
    run(LimbMulAir::new(k, boost), log_n_rows, rate, false);
}

#[test]
#[should_panic(expected = "AIR constraint check failed")]
fn test_reject_corrupted_limb() {
    run(LimbMulAir::new(1, false), 8, 1, true);
}

#[test]
#[should_panic(expected = "AIR constraint check failed")]
fn test_reject_corrupted_limb_boost() {
    run(LimbMulAir::new(1, true), 8, 1, true);
}
