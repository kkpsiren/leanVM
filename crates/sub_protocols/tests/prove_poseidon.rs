use std::time::Instant;

use backend::*;
use lean_vm::{
    EF, ExtraDataForBuses, F, HALF_DIGEST_LEN, POSEIDON_8_COL_ADDR_LEFT_HI, POSEIDON_8_COL_ADDR_LEFT_LO,
    POSEIDON_8_COL_FLAG_OUT4, POSEIDON_8_COL_INPUT_START, POSEIDON_8_COL_MULTIPLICITY, POSEIDON_8_COL_OUT_LO,
    POSEIDON_8_COL_ROUND_START, Poseidon8Precompile, compute_poseidon8_witness, fill_trace_poseidon_8,
    num_cols_poseidon_8,
};
use rand::{RngExt, SeedableRng, rngs::StdRng};
use sub_protocols::{
    AirSumcheckSession, OuterSumcheckSession, natural_ordering_point_for_session, prove_batched_air_sumcheck,
};

#[test]
fn test_prove_poseidon_8() {
    // LOG_N_ROWS=20 cargo test --release --package sub_protocols --test prove_poseidon_8 -- test_prove_poseidon_8 --exact --nocapture
    let log_n_rows: usize = std::env::var("LOG_N_ROWS").unwrap_or("11".to_string()).parse().unwrap();
    init_tracing();
    prove_air_poseidon_8(log_n_rows);
}

#[allow(clippy::too_many_lines)]
fn prove_air_poseidon_8(log_n_rows: usize) {
    let n_rows = 1 << log_n_rows;
    let mut rng = StdRng::seed_from_u64(0);
    let n_cols = num_cols_poseidon_8();
    let mut trace: Vec<ArenaVec<F>> = (0..n_cols).map(|_| ArenaVec::filled(F::ZERO, n_rows)).collect();
    for t in trace.iter_mut().skip(POSEIDON_8_COL_INPUT_START).take(WIDTH) {
        *t = ArenaVec::from_iter((0..n_rows).map(|_| rng.random()));
    }
    trace[POSEIDON_8_COL_MULTIPLICITY] = ArenaVec::filled(F::ONE, n_rows);
    trace[POSEIDON_8_COL_FLAG_OUT4] = ArenaVec::filled(F::ONE, n_rows);
    trace[POSEIDON_8_COL_ADDR_LEFT_LO] = ArenaVec::filled(F::ZERO, n_rows);
    trace[POSEIDON_8_COL_ADDR_LEFT_HI] = ArenaVec::filled(F::from_usize(HALF_DIGEST_LEN), n_rows);

    // Fill the per-round witness columns + outputs from the inputs.
    // The AIR's transition constraints require a consistent Poseidon1 permutation
    // trace, otherwise sumcheck verification fails.
    #[allow(clippy::needless_range_loop)]
    for row in 0..n_rows {
        let input: [F; WIDTH] = std::array::from_fn(|i| trace[POSEIDON_8_COL_INPUT_START + i][row]);
        let (aux, perm_state) = compute_poseidon8_witness(input);
        // Compression rows (flag_permute = 0): `out_lo` holds the Davies-Meyer
        // output; `out_hi` is left zero (AIR-unconstrained for compression).
        for i in 0..WIDTH / 2 {
            trace[POSEIDON_8_COL_OUT_LO + i][row] = perm_state[i] + input[i];
        }
        for (i, v) in aux.iter().enumerate() {
            trace[POSEIDON_8_COL_ROUND_START + i][row] = *v;
        }
    }

    fill_trace_poseidon_8(&mut trace);

    let air = Poseidon8Precompile::<false>;
    let n_constraints = air.n_constraints();
    let air_degree = air.degree_air();

    let whir_config_builder = WhirConfigBuilder {
        folding_factor: FoldingFactor::new(7, 4),
        soundness_type: SecurityAssumption::JohnsonBound,
        pow_bits: 16,
        max_num_variables_to_send_coeffs: 9,
        rs_domain_initial_reduction_factor: 5,
        security_level: 124,
        starting_log_inv_rate: 1,
    };

    let packed_n_vars = log2_ceil_usize(n_cols << log_n_rows);
    let whir_config = WhirConfig::new(&whir_config_builder, packed_n_vars);

    let mut prover_state = ProverState::<EF, _>::new(*get_poseidon8(), Default::default());

    let time = Instant::now();

    let mut commitmed_pol = ArenaVec::filled(F::ZERO, (n_cols << log_n_rows).next_power_of_two());
    for (i, col) in trace.iter().enumerate() {
        commitmed_pol[i << log_n_rows..(i + 1) << log_n_rows].copy_from_slice(col);
    }
    let committed_pol = MleOwned::Base(commitmed_pol);
    let witness = whir_config.commit(&mut prover_state, &committed_pol, n_cols << log_n_rows);

    let alpha = prover_state.sample();
    let air_alpha_powers: Vec<EF> = alpha.powers().collect_n(n_constraints);
    // BUS=false => `logup_alphas_eq_poly` is unused; only `alpha_powers` matter.
    let extra_data = ExtraDataForBuses::new(&[], air_alpha_powers);
    prover_state.duplex();
    let eq_factor: Vec<EF> = prover_state.sample_vec(log_n_rows);
    let column_refs: Vec<&[F]> = trace.iter().map(|c| c.as_slice()).collect();
    let packed = MleGroupRef::<EF>::Base(column_refs).pack();

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

    println!(
        "{} Poseidons / s",
        (n_rows as f64 / time.elapsed().as_secs_f64()) as usize
    );

    let mut verifier_state =
        VerifierState::<EF, _>::new(prover_state.into_proof(), *get_poseidon8(), Default::default()).unwrap();

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
    let constraint_eval =
        <Poseidon8Precompile<false> as SumcheckComputation<EF>>::eval_extension(&air, &col_evals_v, &extra_data);

    let natural_ordering_point_v = natural_ordering_point_for_session(&sumcheck_air_point_v.0, log_n_rows);
    let eq_val = MultilinearPoint(eq_factor_v).eq_poly_outside(&MultilinearPoint(natural_ordering_point_v.clone()));
    assert_eq!(eq_val * constraint_eval, claimed_air_final_value);

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
}
