from snark_lib import *
from whir import *
from hashing import *

N_TABLES = N_TABLES_PLACEHOLDER

LOGUP_GKR_N_VARS_TO_SEND_COEFFS = LOGUP_GKR_N_VARS_TO_SEND_COEFFS_PLACEHOLDER
LOGUP_GKR_N_COEFFS_SENT = 2**LOGUP_GKR_N_VARS_TO_SEND_COEFFS

MIN_LOG_N_ROWS_PER_TABLE = MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MAX_LOG_N_ROWS_PER_TABLE = MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER
MIN_LOG_MEMORY_SIZE = MIN_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_LOG_MEMORY_SIZE = MAX_LOG_MEMORY_SIZE_PLACEHOLDER
MAX_BUS_WIDTH = MAX_BUS_WIDTH_PLACEHOLDER
TOTAL_NUM_AIR_CONSTRAINTS = TOTAL_NUM_AIR_CONSTRAINTS_PLACEHOLDER
N_AIR_CONSTRAINTS = N_AIR_CONSTRAINTS_PLACEHOLDER  # n_constraints per table_index

LOGUP_MEMORY_DOMAINSEP = LOGUP_MEMORY_DOMAINSEP_PLACEHOLDER
LOGUP_BYTECODE_DOMAINSEP = LOGUP_BYTECODE_DOMAINSEP_PLACEHOLDER
EXECUTION_TABLE_INDEX = EXECUTION_TABLE_INDEX_PLACEHOLDER

ONE_BUSES_DOMSEPS = ONE_BUSES_DOMSEPS_PLACEHOLDER  # [[_; num_buses]; N_TABLES]
ONE_BUSES_DATA_COLS = ONE_BUSES_DATA_COLS_PLACEHOLDER  # [[[_; num_data]; num_buses]; N_TABLES]
ONE_BUSES_DATA_OFFSETS = ONE_BUSES_DATA_OFFSETS_PLACEHOLDER  # [[[_; num_data]; num_buses]; N_TABLES]
ONE_BUSES_NEW_COLS = ONE_BUSES_NEW_COLS_PLACEHOLDER  # [[[_; n_new]; num_buses]; N_TABLES]

NUM_COLS_AIR = NUM_COLS_AIR_PLACEHOLDER
MAX_NUM_COLS_AIR = MAX_NUM_COLS_AIR_PLACEHOLDER  # max(NUM_COLS_AIR[t] for t in 0..N_TABLES)
ONE_BUSES_ALL_COLS = ONE_BUSES_ALL_COLS_PLACEHOLDER  # [[col, ...], _; N_TABLES] — sorted union of cols across all Multiplicity::One buses per table

AIR_DEGREES = AIR_DEGREES_PLACEHOLDER  # [_; N_TABLES]
MAX_AIR_FULL_DEGREE = MAX_AIR_FULL_DEGREE_PLACEHOLDER
N_AIR_COLUMNS = N_AIR_COLUMNS_PLACEHOLDER  # [_; N_TABLES]
N_AIR_SHIFT_COLUMNS = N_AIR_SHIFT_COLUMNS_PLACEHOLDER  # [_; N_TABLES] — by convention, shift column j of table t is column j
AIR_ALPHA_OFFSETS = AIR_ALPHA_OFFSETS_PLACEHOLDER  # [_; N_TABLES], # AIR_ALPHA_OFFSETS[t] = sum(N_AIR_CONSTRAINTS[k] for k in range(t))

N_INSTRUCTION_COLUMNS = N_INSTRUCTION_COLUMNS_PLACEHOLDER
N_COMMITTED_EXEC_COLUMNS = N_COMMITTED_EXEC_COLUMNS_PLACEHOLDER

LOG_GUEST_BYTECODE_LEN = LOG_GUEST_BYTECODE_LEN_PLACEHOLDER
EXEC_COL_PC = COL_PC_PLACEHOLDER
TOTAL_WHIR_STATEMENTS = TOTAL_WHIR_STATEMENTS_PLACEHOLDER
STARTING_PC = STARTING_PC_PLACEHOLDER
ENDING_PC = ENDING_PC_PLACEHOLDER
BYTECODE_POINT_N_VARS = LOG_GUEST_BYTECODE_LEN + log2_ceil(N_INSTRUCTION_COLUMNS)
BYTECODE_ZERO_EVAL = BYTECODE_ZERO_EVAL_PLACEHOLDER
BYTECODE_CLAIM_SIZE = (BYTECODE_POINT_N_VARS + 1) * DIM
BYTECODE_CLAIM_SIZE_PADDED = next_multiple_of(BYTECODE_CLAIM_SIZE, DIGEST_LEN)
INNER_PUBLIC_MEMORY_LOG_SIZE = 3  # public input = 1 hash digest = 8 field elements
PUB_INPUT_SIZE = DIGEST_LEN  # the public input is a single digest


def recursion(inner_public_memory, initial_fiat_shamir_cap):
    proof_transcript_size_buf = Array(1)
    hint_witness("proof_transcript_size", proof_transcript_size_buf)
    proof_transcript = Array(proof_transcript_size_buf[0])
    hint_witness("proof_transcript", proof_transcript)
    fs1 = fs_new(proof_transcript, initial_fiat_shamir_cap)

    fs2 = fs_observe(fs1, inner_public_memory, PUB_INPUT_SIZE)  # observe public input (the data digest)

    # table dims
    debug_assert(N_TABLES + 1 < DIGEST_LEN)
    fs3, dims = fs_receive_chunks(fs2, 1)
    for i in unroll(N_TABLES + 2, 8):
        assert dims[i] == 0
    whir_log_inv_rate = dims[0]
    log_memory = dims[1]
    table_log_heights = dims + 2

    assert MIN_WHIR_LOG_INV_RATE <= whir_log_inv_rate
    assert whir_log_inv_rate <= MAX_WHIR_LOG_INV_RATE

    table_heights = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        table_log_height = table_log_heights[i]
        assert table_log_height <= MAX_LOG_N_ROWS_PER_TABLE[i]
        assert MIN_LOG_N_ROWS_PER_TABLE <= table_log_height
        table_heights[i] = two_exp(table_log_height)

    sorted_tables = Array(N_TABLES) # sorted_tables[0] is the index of the biggest table, sorted_tables[1] is the index of the second biggest table, etc
    hint_witness("table_sort_perm", sorted_tables)
    # Force table_sort_perm to be a permutation of {0..N_TABLES-1}
    perm_seen = Array(N_TABLES)
    for i in unroll(0, N_TABLES):
        p = sorted_tables[i]
        assert p < N_TABLES
        perm_seen[p] = i
    
    for i in unroll(0, N_TABLES - 1):
        height_curr = table_log_heights[sorted_tables[i]]
        height_next = table_log_heights[sorted_tables[i + 1]]
        assert height_next <= height_curr
        if height_curr == height_next:
            assert sorted_tables[i] < sorted_tables[i + 1]

    assert MIN_LOG_MEMORY_SIZE <= log_memory
    assert log_memory <= MAX_LOG_MEMORY_SIZE
    assert LOG_GUEST_BYTECODE_LEN <= log_memory

    log_max_table_height = table_log_heights[sorted_tables[0]]  # largest table's log height
    assert log_max_table_height <= log_memory
    log_n_cycles = table_log_heights[EXECUTION_TABLE_INDEX]

    log_bytecode_padded = maximum(LOG_GUEST_BYTECODE_LEN, log_max_table_height)

    stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode_padded, table_heights)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - whir_log_inv_rate

    n_vars_logup_gkr = compute_total_gkr_n_vars(log_memory, log_bytecode_padded, table_heights)

    n_buses_per_table = Array(N_TABLES) # indexed by table_index
    n_cols_per_table = Array(N_TABLES) # indexed by table_index
    for i in unroll(0, N_TABLES):
        n_buses_per_table[i] = len(ONE_BUSES_DOMSEPS[i]) + 1 # + 1 for the precompile bus interraction (the rest is memory / bytecode interractions)
        n_cols_per_table[i] = NUM_COLS_AIR[i]

    gkr_table_base_offset = Array(N_TABLES)
    stacked_table_base_offset = Array(N_TABLES)
    gkr_cumul_buf = Array(N_TABLES + 1)
    stacked_cumul_buf = Array(N_TABLES + 1)
    gkr_cumul_buf[0] = two_exp(log_memory) + two_exp(log_bytecode_padded)
    stacked_cumul_buf[0] = two_exp(log_memory) * 2 + two_exp(log_bytecode_padded)
    for sorted_pos in unroll(0, N_TABLES):
        ti = sorted_tables[sorted_pos]
        gkr_table_base_offset[ti] = gkr_cumul_buf[sorted_pos]
        stacked_table_base_offset[ti] = stacked_cumul_buf[sorted_pos]
        n_rows = table_heights[ti]
        gkr_cumul_buf[sorted_pos + 1] = gkr_cumul_buf[sorted_pos] + n_rows * n_buses_per_table[ti]
        stacked_cumul_buf[sorted_pos + 1] = stacked_cumul_buf[sorted_pos] + n_rows * n_cols_per_table[ti]

    num_oods = get_num_oods(whir_log_inv_rate, stacked_n_vars)
    num_ood_at_commitment = num_oods[0]
    fs4, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_commitment(fs3, num_ood_at_commitment)

    fs5, logup_c = fs_sample_ef(fs4)

    fs6 = fs_duplex(fs5)
    fs7, logup_alphas = fs_sample_many_ef(fs6, log2_ceil(MAX_BUS_WIDTH))

    logup_alphas_eq_poly = compute_eq_mle_extension(logup_alphas, log2_ceil(MAX_BUS_WIDTH))

    # LOGUP

    fs8, quotient_gkr, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(fs7, n_vars_logup_gkr)
    set_to_5_zeros(quotient_gkr)

    memory_and_acc_prefix = multilinear_location_prefix(0, n_vars_logup_gkr - log_memory, point_gkr)

    fs9, value_acc = fs_receive_ef_inlined(fs8, 1)
    fs10, value_memory = fs_receive_ef_inlined(fs9, 1)

    retrieved_numerators_value_0 = opposite_extension_ret(mul_extension_ret(memory_and_acc_prefix, value_acc))

    value_index = mle_of_01234567_etc(point_gkr + (n_vars_logup_gkr - log_memory) * DIM, log_memory)
    fingerprint_memory = fingerprint_2(LOGUP_MEMORY_DOMAINSEP, value_index, value_memory, logup_alphas_eq_poly)
    retrieved_denominators_value_0 = mul_extension_ret(
        memory_and_acc_prefix, sub_extension_ret(logup_c, fingerprint_memory)
    )

    bytecode_section_offset = two_exp(log_memory)

    bytecode_and_acc_point = point_gkr + (n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN) * DIM
    bytecode_multilinear_location_prefix = multilinear_location_prefix(
        bytecode_section_offset / 2**LOG_GUEST_BYTECODE_LEN, n_vars_logup_gkr - LOG_GUEST_BYTECODE_LEN, point_gkr
    )
    bytecode_padded_multilinear_location_prefix = multilinear_location_prefix(
        bytecode_section_offset / two_exp(log_bytecode_padded), n_vars_logup_gkr - log_bytecode_padded, point_gkr
    )
    # Build padded claim data: [point | value | zero padding]
    bytecode_claim = Array(BYTECODE_CLAIM_SIZE_PADDED)
    copy_many_ef(bytecode_and_acc_point, bytecode_claim, LOG_GUEST_BYTECODE_LEN)
    copy_many_ef(
        logup_alphas + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        bytecode_claim + LOG_GUEST_BYTECODE_LEN * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    hint_witness("bytecode_value_hint", bytecode_claim + BYTECODE_POINT_N_VARS * DIM)
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        bytecode_claim[k] = 0
    bytecode_value = bytecode_claim + BYTECODE_POINT_N_VARS * DIM
    n_corr = log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)
    bytecode_value_corrected_buf = Array(n_corr + 1)
    bytecode_value_corrected_buf[0] = bytecode_value
    for i in unroll(0, n_corr):
        bytecode_value_corrected_buf[i + 1] = mul_extension_ret(
            bytecode_value_corrected_buf[i], one_minus_self_extension_ret(logup_alphas + i * DIM)
        )

    fs11, value_bytecode_acc = fs_receive_ef_inlined(fs10, 1)
    retrieved_numerators_value_1 = sub_extension_ret(
        retrieved_numerators_value_0, mul_extension_ret(bytecode_multilinear_location_prefix, value_bytecode_acc)
    )

    bytecode_index_value = mle_of_01234567_etc(bytecode_and_acc_point, LOG_GUEST_BYTECODE_LEN)
    retrieved_denominators_value_1 = add_extension_ret(
        retrieved_denominators_value_0,
        mul_extension_ret(
            bytecode_multilinear_location_prefix,
            sub_extension_ret(
                logup_c,
                add_extension_ret(
                    bytecode_value_corrected_buf[n_corr],
                    add_extension_ret(
                        mul_extension_ret(bytecode_index_value, logup_alphas_eq_poly + N_INSTRUCTION_COLUMNS * DIM),
                        mul_base_extension_ret(
                            LOGUP_BYTECODE_DOMAINSEP, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM
                        ),
                    ),
                ),
            ),
        ),
    )
    retrieved_denominators_value_2 = add_extension_ret(
        retrieved_denominators_value_1,
        mul_extension_ret(
            bytecode_padded_multilinear_location_prefix,
            mle_of_zeros_then_ones_pow2(
                point_gkr + (n_vars_logup_gkr - log_bytecode_padded) * DIM,
                LOG_GUEST_BYTECODE_LEN,
                log_bytecode_padded,
            ),
        ),
    )

    # Per-table data accumulators (indexed by table_index).
    bus_numerators_values = Array(N_TABLES * DIM)
    bus_denominators_values = Array(N_TABLES * DIM)
    pcs_inner_points = Array(N_TABLES)
    pcs_vals_logup = Array(N_TABLES * MAX_NUM_COLS_AIR)
    pcs_vals_air = Array(N_TABLES * MAX_NUM_COLS_AIR)
    pcs_shifts_air = Array(N_TABLES * MAX_NUM_COLS_AIR)

    # fs / numerator / denominator threaded across tables (and, within each table, across buses)
    fs_tab_buf = Array(N_TABLES + 1)
    rnum_tab_buf = Array(N_TABLES + 1)
    rden_tab_buf = Array(N_TABLES + 1)
    fs_tab_buf[0] = fs11
    rnum_tab_buf[0] = retrieved_numerators_value_1
    rden_tab_buf[0] = retrieved_denominators_value_2
    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        offset0 = gkr_table_base_offset[table_index]

        inner_point = point_gkr + (n_vars_logup_gkr - log_n_rows) * DIM
        pcs_inner_points[table_index] = inner_point

        # Bus (data flow between tables — Multiplicity::Column)
        prefix = multilinear_location_prefix(offset0 / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr)

        fs_sel, eval_on_selector = fs_receive_ef_inlined(fs_tab_buf[table_index], 1)
        rnum_after_sel = add_extension_ret(rnum_tab_buf[table_index], mul_extension_ret(prefix, eval_on_selector))

        fs_data, eval_on_data = fs_receive_ef_inlined(fs_sel, 1)
        rden_after_data = add_extension_ret(rden_tab_buf[table_index], mul_extension_ret(prefix, eval_on_data))

        copy_5(eval_on_selector, bus_numerators_values + table_index * DIM)
        copy_5(eval_on_data, bus_denominators_values + table_index * DIM)

        # Multiplicity::One buses (bytecode lookup + memory lookups).
        n_one_buses = len(ONE_BUSES_DOMSEPS[table_index])
        fs_bus_buf = Array(n_one_buses + 1)
        rnum_bus_buf = Array(n_one_buses + 1)
        rden_bus_buf = Array(n_one_buses + 1)
        offset_bus_buf = Array(n_one_buses + 1)
        fs_bus_buf[0] = fs_data
        rnum_bus_buf[0] = rnum_after_sel
        rden_bus_buf[0] = rden_after_data
        offset_bus_buf[0] = offset0 + n_rows
        for one_bus_idx in unroll(0, n_one_buses):
            domsep = ONE_BUSES_DOMSEPS[table_index][one_bus_idx]
            n_new = len(ONE_BUSES_NEW_COLS[table_index][one_bus_idx])
            n_data = len(ONE_BUSES_DATA_COLS[table_index][one_bus_idx])

            fs_bus_buf[one_bus_idx + 1], new_evals = fs_receive_ef_inlined(fs_bus_buf[one_bus_idx], n_new)

            for i in unroll(0, n_new):
                new_col = ONE_BUSES_NEW_COLS[table_index][one_bus_idx][i]
                pcs_vals_logup[table_index * MAX_NUM_COLS_AIR + new_col] = new_evals + i * DIM

            data_evals = Array(n_data * DIM)
            for i in unroll(0, n_data):
                data_col = ONE_BUSES_DATA_COLS[table_index][one_bus_idx][i]
                data_ofs = ONE_BUSES_DATA_OFFSETS[table_index][one_bus_idx][i]
                src = pcs_vals_logup[table_index * MAX_NUM_COLS_AIR + data_col]
                if data_ofs == 0:
                    copy_5(src, data_evals + i * DIM)
                if data_ofs != 0:
                    copy_5(add_base_extension_ret(data_ofs, src), data_evals + i * DIM)

            pref = multilinear_location_prefix(
                offset_bus_buf[one_bus_idx] / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr
            )
            rnum_bus_buf[one_bus_idx + 1] = add_extension_ret(rnum_bus_buf[one_bus_idx], pref)
            fingerp = fingerprint_n(domsep, data_evals, n_data, logup_alphas_eq_poly)
            rden_bus_buf[one_bus_idx + 1] = add_extension_ret(
                rden_bus_buf[one_bus_idx],
                mul_extension_ret(pref, sub_extension_ret(logup_c, fingerp)),
            )
            offset_bus_buf[one_bus_idx + 1] = offset_bus_buf[one_bus_idx] + n_rows
        fs_tab_buf[table_index + 1] = fs_bus_buf[n_one_buses]
        rnum_tab_buf[table_index + 1] = rnum_bus_buf[n_one_buses]
        rden_tab_buf[table_index + 1] = rden_bus_buf[n_one_buses]

    # Final logup adjustment (padding)
    retrieved_denominators_value_final = add_extension_ret(
        rden_tab_buf[N_TABLES],
        mle_of_zeros_then_ones(point_gkr, gkr_cumul_buf[N_TABLES], n_vars_logup_gkr),
    )

    copy_5(rnum_tab_buf[N_TABLES], numerators_value)
    copy_5(retrieved_denominators_value_final, denominators_value)
    fs12 = fs_tab_buf[N_TABLES]

    memory_and_acc_point = point_gkr + (n_vars_logup_gkr - log_memory) * DIM

    # END OF LOGUP

    # VERIFY BUS AND AIR — back-loaded batched sumcheck

    fs13, air_alpha = fs_sample_ef(fs12)
    air_alpha_powers = powers_const(air_alpha, TOTAL_NUM_AIR_CONSTRAINTS)

    initial_sum_buf = Array(N_TABLES + 1)
    initial_sum_buf[0] = ZERO_VEC_PTR
    for table_index in unroll(0, N_TABLES):
        alpha_offset = AIR_ALPHA_OFFSETS[table_index]
        bus_numerator_value = bus_numerators_values + table_index * DIM
        bus_denominator_value = bus_denominators_values + table_index * DIM

        signed_numerator: Imm
        if table_index == EXECUTION_TABLE_INDEX:
            signed_numerator = bus_numerator_value
        else:
            signed_numerator = opposite_extension_ret(bus_numerator_value)
        bus_final_value_0 = mul_extension_ret(air_alpha_powers + alpha_offset * DIM, signed_numerator)
        bus_final_value_1 = add_extension_ret(
            bus_final_value_0,
            mul_extension_ret(
                air_alpha_powers + (alpha_offset + 1) * DIM,
                sub_extension_ret(logup_c, bus_denominator_value),
            ),
        )
        initial_sum_buf[table_index + 1] = add_extension_ret(initial_sum_buf[table_index], bus_final_value_1)

    n_max = log_max_table_height
    # Batched AIR sumcheck:
    fs14, all_challenges, batched_air_final_value = sumcheck_verify_reversed(
        fs13, n_max, initial_sum_buf[N_TABLES], MAX_AIR_FULL_DEGREE
    )

    fs_air_buf = Array(N_TABLES + 1)
    check_sum_buf = Array(N_TABLES + 1)
    fs_air_buf[0] = fs14
    check_sum_buf[0] = ZERO_VEC_PTR
    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_flat_columns = N_AIR_COLUMNS[table_index]
        n_shift_columns = N_AIR_SHIFT_COLUMNS[table_index]
        alpha_offset = AIR_ALPHA_OFFSETS[table_index]

        fs_air_buf[table_index + 1], inner_evals = fs_receive_ef_inlined(
            fs_air_buf[table_index], n_flat_columns + n_shift_columns
        )

        air_constraints_eval = evaluate_air_constraints(
            table_index, inner_evals, air_alpha_powers + alpha_offset * DIM, logup_alphas_eq_poly
        )

        bus_point = pcs_inner_points[table_index]
        eq_val = poly_eq_extension_dynamic_ret(bus_point, all_challenges, log_n_rows)

        k_t = product_first_n(all_challenges + log_n_rows * DIM, n_max - log_n_rows)

        contribution = mul_extension_ret(k_t, mul_extension_ret(eq_val, air_constraints_eval))
        check_sum_buf[table_index + 1] = add_extension_ret(check_sum_buf[table_index], contribution)

        # AIR block (i=1): all flat cols 0..n_flat_columns populated; shifts 0..n_shift_columns populated.
        for i in unroll(0, n_flat_columns):
            pcs_vals_air[table_index * MAX_NUM_COLS_AIR + i] = inner_evals + i * DIM
        if n_shift_columns != 0:
            evals_shift = inner_evals + n_flat_columns * DIM
            for i in unroll(0, n_shift_columns):
                pcs_shifts_air[table_index * MAX_NUM_COLS_AIR + i] = evals_shift + i * DIM

    # verify that the AIR-batched sumcheck is valid
    copy_5(check_sum_buf[N_TABLES], batched_air_final_value)
    fs15 = fs_air_buf[N_TABLES]

    fs16, public_memory_random_point = fs_sample_many_ef(fs15, INNER_PUBLIC_MEMORY_LOG_SIZE)
    poly_eq_public_mem = compute_eq_mle_extension(public_memory_random_point, INNER_PUBLIC_MEMORY_LOG_SIZE)
    public_memory_eval = Array(DIM)
    dot_product_be(inner_public_memory, poly_eq_public_mem, public_memory_eval, 2**INNER_PUBLIC_MEMORY_LOG_SIZE)

    # WHIR BASE
    fs17 = fs_duplex(fs16)
    fs18, combination_randomness_gen = fs_sample_ef(fs17)
    combination_randomness_powers = powers(combination_randomness_gen, num_ood_at_commitment + TOTAL_WHIR_STATEMENTS)
    whir_sum_0 = Array(DIM)
    dot_product_ee_dynamic(whir_base_ood_evals, combination_randomness_powers, whir_sum_0, num_ood_at_commitment)
    curr_randomness_0 = combination_randomness_powers + num_ood_at_commitment * DIM

    whir_sum_1 = add_extension_ret(mul_extension_ret(value_memory, curr_randomness_0), whir_sum_0)
    curr_randomness_1 = curr_randomness_0 + DIM
    whir_sum_2 = add_extension_ret(mul_extension_ret(value_acc, curr_randomness_1), whir_sum_1)
    curr_randomness_2 = curr_randomness_1 + DIM
    whir_sum_3 = add_extension_ret(mul_extension_ret(public_memory_eval, curr_randomness_2), whir_sum_2)
    curr_randomness_3 = curr_randomness_2 + DIM
    whir_sum_4 = add_extension_ret(mul_extension_ret(value_bytecode_acc, curr_randomness_3), whir_sum_3)
    curr_randomness_4 = curr_randomness_3 + DIM

    # whir_sum / curr_randomness threaded across tables (and, within each table, across columns)
    ws_tab_buf = Array(N_TABLES + 1)
    curr_tab_buf = Array(N_TABLES + 1)
    ws_tab_buf[0] = whir_sum_4
    curr_tab_buf[0] = curr_randomness_4
    for table_index in unroll(0, N_TABLES):
        ws_pc: Imm
        curr_pc: Imm
        if table_index == EXECUTION_TABLE_INDEX:
            ws_pc_a = add_extension_ret(
                mul_extension_ret(embed_in_ef(STARTING_PC), curr_tab_buf[table_index]), ws_tab_buf[table_index]
            )
            ws_pc = add_extension_ret(
                mul_extension_ret(embed_in_ef(ENDING_PC), curr_tab_buf[table_index] + DIM), ws_pc_a
            )
            curr_pc = curr_tab_buf[table_index] + 2 * DIM
        else:
            ws_pc = ws_tab_buf[table_index]
            curr_pc = curr_tab_buf[table_index]

        # LOGUP
        n_logup_cols = len(ONE_BUSES_ALL_COLS[table_index])
        ws_logup_buf = Array(n_logup_cols + 1)
        curr_logup_buf = Array(n_logup_cols + 1)
        ws_logup_buf[0] = ws_pc
        curr_logup_buf[0] = curr_pc
        for k in unroll(0, n_logup_cols):
            col = ONE_BUSES_ALL_COLS[table_index][k]
            ws_logup_buf[k + 1] = add_extension_ret(
                mul_extension_ret(pcs_vals_logup[table_index * MAX_NUM_COLS_AIR + col], curr_logup_buf[k]),
                ws_logup_buf[k],
            )
            curr_logup_buf[k + 1] = curr_logup_buf[k] + DIM

        # AIR
        n_shift = N_AIR_SHIFT_COLUMNS[table_index]
        ws_shift_buf = Array(n_shift + 1)
        curr_shift_buf = Array(n_shift + 1)
        ws_shift_buf[0] = ws_logup_buf[n_logup_cols]
        curr_shift_buf[0] = curr_logup_buf[n_logup_cols]
        for j in unroll(0, n_shift):
            ws_shift_buf[j + 1] = add_extension_ret(
                mul_extension_ret(pcs_shifts_air[table_index * MAX_NUM_COLS_AIR + j], curr_shift_buf[j]),
                ws_shift_buf[j],
            )
            curr_shift_buf[j + 1] = curr_shift_buf[j] + DIM
        n_cols = N_AIR_COLUMNS[table_index]
        ws_col_buf = Array(n_cols + 1)
        curr_col_buf = Array(n_cols + 1)
        ws_col_buf[0] = ws_shift_buf[n_shift]
        curr_col_buf[0] = curr_shift_buf[n_shift]
        for j in unroll(0, n_cols):
            ws_col_buf[j + 1] = add_extension_ret(
                mul_extension_ret(pcs_vals_air[table_index * MAX_NUM_COLS_AIR + j], curr_col_buf[j]),
                ws_col_buf[j],
            )
            curr_col_buf[j + 1] = curr_col_buf[j] + DIM
        ws_tab_buf[table_index + 1] = ws_col_buf[n_cols]
        curr_tab_buf[table_index + 1] = curr_col_buf[n_cols]
    whir_sum_final = ws_tab_buf[N_TABLES]

    fs19, folding_randomness_global, s_0, final_value, end_sum = whir_open(
        fs18,
        stacked_n_vars,
        whir_log_inv_rate,
        whir_base_root,
        whir_base_ood_points,
        combination_randomness_powers,
        whir_sum_final,
    )

    curr_randomness_b0 = combination_randomness_powers + num_ood_at_commitment * DIM

    eq_memory_and_acc_point = poly_eq_extension_dynamic_ret(
        folding_randomness_global + (stacked_n_vars - log_memory) * DIM,
        memory_and_acc_point,
        log_memory,
    )
    prefix_memory = multilinear_location_prefix(0, stacked_n_vars - log_memory, folding_randomness_global)
    s_1 = add_extension_ret(
        s_0,
        mul_extension_ret(mul_extension_ret(curr_randomness_b0, prefix_memory), eq_memory_and_acc_point),
    )
    curr_randomness_b1 = curr_randomness_b0 + DIM

    prefix_acc_memory = multilinear_location_prefix(1, stacked_n_vars - log_memory, folding_randomness_global)
    s_2 = add_extension_ret(
        s_1,
        mul_extension_ret(mul_extension_ret(curr_randomness_b1, prefix_acc_memory), eq_memory_and_acc_point),
    )
    curr_randomness_b2 = curr_randomness_b1 + DIM

    eq_pub_mem = Array(DIM)
    poly_eq_ee(
        folding_randomness_global + (stacked_n_vars - INNER_PUBLIC_MEMORY_LOG_SIZE) * DIM,
        public_memory_random_point,
        eq_pub_mem,
        INNER_PUBLIC_MEMORY_LOG_SIZE,
    )
    prefix_pub_mem = multilinear_location_prefix(
        0, stacked_n_vars - INNER_PUBLIC_MEMORY_LOG_SIZE, folding_randomness_global
    )
    s_3 = add_extension_ret(
        s_2,
        mul_extension_ret(mul_extension_ret(curr_randomness_b2, prefix_pub_mem), eq_pub_mem),
    )
    curr_randomness_b3 = curr_randomness_b2 + DIM

    bytecode_acc_layout_offset = two_exp(log_memory) * 2  # memory + acc_memory

    eq_bytecode_acc = Array(DIM)
    poly_eq_ee(
        folding_randomness_global + (stacked_n_vars - LOG_GUEST_BYTECODE_LEN) * DIM,
        bytecode_and_acc_point,
        eq_bytecode_acc,
        LOG_GUEST_BYTECODE_LEN,
    )
    prefix_bytecode_acc = multilinear_location_prefix(
        bytecode_acc_layout_offset / 2**LOG_GUEST_BYTECODE_LEN,
        stacked_n_vars - LOG_GUEST_BYTECODE_LEN,
        folding_randomness_global,
    )
    s_4 = add_extension_ret(
        s_3,
        mul_extension_ret(mul_extension_ret(curr_randomness_b3, prefix_bytecode_acc), eq_bytecode_acc),
    )
    curr_randomness_b4 = curr_randomness_b3 + DIM

    # s / curr_randomness threaded across tables (and, within each table, across columns)
    s_tab_buf = Array(N_TABLES + 1)
    curr_tab_buf2 = Array(N_TABLES + 1)
    s_tab_buf[0] = s_4
    curr_tab_buf2[0] = curr_randomness_b4
    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        total_num_cols = NUM_COLS_AIR[table_index]
        table_offset = stacked_table_base_offset[table_index]

        s_pc: Imm
        curr_pc2: Imm
        if table_index == EXECUTION_TABLE_INDEX:
            prefix_pc_start = multilinear_location_prefix(
                table_offset + EXEC_COL_PC * two_exp(log_n_cycles),
                stacked_n_vars,
                folding_randomness_global,
            )
            s_pc_a = add_extension_ret(s_tab_buf[table_index], mul_extension_ret(curr_tab_buf2[table_index], prefix_pc_start))

            prefix_pc_end = multilinear_location_prefix(
                table_offset + (EXEC_COL_PC + 1) * two_exp(log_n_cycles) - 1,
                stacked_n_vars,
                folding_randomness_global,
            )
            s_pc = add_extension_ret(s_pc_a, mul_extension_ret(curr_tab_buf2[table_index] + DIM, prefix_pc_end))
            curr_pc2 = curr_tab_buf2[table_index] + 2 * DIM
        else:
            s_pc = s_tab_buf[table_index]
            curr_pc2 = curr_tab_buf2[table_index]

        column_prefixes = compute_column_prefixes(
            table_offset / n_rows,
            stacked_n_vars - log_n_rows,
            folding_randomness_global,
            total_num_cols,
        )
        inner_folding = folding_randomness_global + (stacked_n_vars - log_n_rows) * DIM
        n_shift_columns = N_AIR_SHIFT_COLUMNS[table_index]

        # LOGUP
        eq_factor_logup = poly_eq_extension_dynamic_ret(pcs_inner_points[table_index], inner_folding, log_n_rows)
        n_logup = len(ONE_BUSES_ALL_COLS[table_index])
        logup_acc_buf = Array(n_logup + 1)
        curr_logup_buf2 = Array(n_logup + 1)
        logup_acc_buf[0] = ZERO_VEC_PTR
        curr_logup_buf2[0] = curr_pc2
        for k in unroll(0, n_logup):
            col = ONE_BUSES_ALL_COLS[table_index][k]
            prefix = column_prefixes + col * DIM
            logup_acc_buf[k + 1] = add_extension_ret(logup_acc_buf[k], mul_extension_ret(curr_logup_buf2[k], prefix))
            curr_logup_buf2[k + 1] = curr_logup_buf2[k] + DIM
        s_after_logup = add_extension_ret(s_pc, mul_extension_ret(logup_acc_buf[n_logup], eq_factor_logup))
        curr_after_logup = curr_logup_buf2[n_logup]

        # AIR
        s_after_shift: Imm
        curr_after_shift: Imm
        if n_shift_columns != 0:
            next_factor = next_mle(all_challenges, inner_folding, log_n_rows)
            shift_sum = dot_product_ee_ret(curr_after_logup, column_prefixes, n_shift_columns)
            s_after_shift = add_extension_ret(s_after_logup, mul_extension_ret(shift_sum, next_factor))
            curr_after_shift = curr_after_logup + n_shift_columns * DIM
        else:
            s_after_shift = s_after_logup
            curr_after_shift = curr_after_logup
        eq_factor_air = poly_eq_extension_dynamic_ret(all_challenges, inner_folding, log_n_rows)
        air_sum = dot_product_ee_ret(curr_after_shift, column_prefixes, N_AIR_COLUMNS[table_index])
        s_tab_buf[table_index + 1] = add_extension_ret(s_after_shift, mul_extension_ret(air_sum, eq_factor_air))
        curr_tab_buf2[table_index + 1] = curr_after_shift + N_AIR_COLUMNS[table_index] * DIM

    copy_5(mul_extension_ret(s_tab_buf[N_TABLES], final_value), end_sum)

    return bytecode_claim


def multilinear_location_prefix(offset, n_vars, point):
    bits = checked_decompose_bits_small_value(offset, n_vars)
    res = poly_eq_base_extension(bits, point, n_vars)
    return res


def compute_column_prefixes(first_col_offset, n_vars, point, n_cols: Const):
    K = log2_ceil(n_cols)
    debug_assert(0 < K)
    debug_assert(K <= n_vars)
    high_n_vars = n_vars - K

    # low factor: eq(., point[high_n_vars:]) for every K-bit pattern
    low_eq = compute_eq_mle_extension(point + high_n_vars * DIM, K)

    # high factors for q = floor(first_col_offset / 2^K) and for the last column's q (q or q+1)
    bits_first = checked_decompose_bits_small_value(first_col_offset, n_vars)
    bits_last = checked_decompose_bits_small_value(first_col_offset + n_cols - 1, n_vars)
    high_eq_lo = poly_eq_base_extension_or_one(bits_first, point, high_n_vars)
    high_eq_hi = poly_eq_base_extension_or_one(bits_last, point, high_n_vars)

    # column_prefixes[w]        = eq(q,   point_high) * low_eq[w]   for w in [0, 2^K)
    # column_prefixes[2^K + w]  = eq(q+1, point_high) * low_eq[w]   for w in [0, 2^K)
    column_prefixes = Array(2 ** (K + 1) * DIM)
    for w in unroll(0, 2**K):
        mul_extension(high_eq_lo, low_eq + w * DIM, column_prefixes + w * DIM)
        mul_extension(high_eq_hi, low_eq + w * DIM, column_prefixes + (2**K + w) * DIM)

    # r = first_col_offset mod 2^K (low K bits; big-endian bits, index n_vars-1 is the LSB)
    r_buf = Array(K)
    r_buf[0] = bits_first[n_vars - 1]
    for i in unroll(1, K):
        r_buf[i] = r_buf[i - 1] + bits_first[n_vars - 1 - i] * 2**i

    # Column j lands at index r + j < 2^K + n_cols <= 2^(K+1).

    return column_prefixes + r_buf[K - 1] * DIM


def fingerprint_2(table_index, data_1, data_2, logup_alphas_eq_poly):
    buff = Array(DIM * 2)
    copy_5(data_1, buff)
    copy_5(data_2, buff + DIM)
    res0 = dot_product_ee_ret(buff, logup_alphas_eq_poly, 2)
    res1 = add_extension_ret(
        res0, mul_base_extension_ret(table_index, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM)
    )
    return res1


@inline
def fingerprint_n(domsep, data_evals, n, logup_alphas_eq_poly):
    res0 = dot_product_ee_ret(data_evals, logup_alphas_eq_poly, n)
    res1 = add_extension_ret(
        res0,
        mul_base_extension_ret(domsep, logup_alphas_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
    )
    return res1


def verify_gkr_quotient(prev_fs, n_vars):
    fs1, nums = fs_receive_ef_inlined(prev_fs, LOGUP_GKR_N_COEFFS_SENT)
    fs2, denoms = fs_receive_ef_inlined(fs1, LOGUP_GKR_N_COEFFS_SENT)

    initial_quotients = Array(LOGUP_GKR_N_COEFFS_SENT * DIM)
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT):
        div_extension(nums + k * DIM, denoms + k * DIM, initial_quotients + k * DIM)
    debug_assert(NUM_REPEATED_ONES <= LOGUP_GKR_N_COEFFS_SENT)
    debug_assert(LOGUP_GKR_N_COEFFS_SENT % NUM_REPEATED_ONES == 0)
    quotient_buf = Array(LOGUP_GKR_N_COEFFS_SENT / NUM_REPEATED_ONES + 1)
    quotient_buf[0] = ZERO_VEC_PTR
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT / NUM_REPEATED_ONES):
        quotient_buf[k + 1] = add_extension_ret(
            quotient_buf[k], sum_continuous_ef(initial_quotients + k * NUM_REPEATED_ONES * DIM, NUM_REPEATED_ONES)
        )

    points = Array(n_vars)
    claims_num = Array(n_vars)
    claims_den = Array(n_vars)

    fs3, initial_point = fs_sample_many_ef(fs2, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)
    points[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = initial_point

    point_poly_eq = compute_eq_mle_extension(initial_point, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)

    first_claim_num = dot_product_ee_ret(nums, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    first_claim_den = dot_product_ee_ret(denoms, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    claims_num[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_num
    claims_den[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_den

    fs_buf = Array(n_vars - LOGUP_GKR_N_VARS_TO_SEND_COEFFS + 1)
    fs_buf[0] = fs3
    for i in range(LOGUP_GKR_N_VARS_TO_SEND_COEFFS, n_vars):
        fs_buf[i - LOGUP_GKR_N_VARS_TO_SEND_COEFFS + 1], points[i], claims_num[i], claims_den[i] = verify_gkr_quotient_step(
            fs_buf[i - LOGUP_GKR_N_VARS_TO_SEND_COEFFS], i, points[i - 1], claims_num[i - 1], claims_den[i - 1]
        )
    fs4 = fs_buf[n_vars - LOGUP_GKR_N_VARS_TO_SEND_COEFFS]

    return (
        fs4,
        quotient_buf[LOGUP_GKR_N_COEFFS_SENT / NUM_REPEATED_ONES],
        points[n_vars - 1],
        claims_num[n_vars - 1],
        claims_den[n_vars - 1],
    )


def verify_gkr_quotient_step(prev_fs, n_vars, point, claim_num, claim_den):
    fs1 = fs_duplex(prev_fs)
    fs2, alpha = fs_sample_ef(fs1)
    alpha_mul_claim_den = mul_extension_ret(alpha, claim_den)
    num_plus_alpha_mul_claim_den = add_extension_ret(claim_num, alpha_mul_claim_den)
    postponed_point = Array((n_vars + 1) * DIM)
    fs3, postponed_value = sumcheck_verify_reversed_helper(
        fs2, n_vars, num_plus_alpha_mul_claim_den, 3, postponed_point
    )
    fs4, inner_evals = fs_receive_ef_inlined(fs3, 4)
    a_num = inner_evals
    b_num = inner_evals + DIM
    a_den = inner_evals + 2 * DIM
    b_den = inner_evals + 3 * DIM
    sum_num, sum_den = sum_2_ef_fractions(a_num, a_den, b_num, b_den)
    sum_den_mul_alpha = mul_extension_ret(sum_den, alpha)
    sum_num_plus_sum_den_mul_alpha = add_extension_ret(sum_num, sum_den_mul_alpha)
    eq_factor = poly_eq_extension_dynamic_ret(point, postponed_point, n_vars)
    mul_extension(sum_num_plus_sum_den_mul_alpha, eq_factor, postponed_value)

    fs5, beta = fs_sample_ef(fs4)

    point_poly_eq = compute_eq_mle_extension(beta, 1)
    new_claim_num = dot_product_ee_ret(inner_evals, point_poly_eq, 2)
    new_claim_den = dot_product_ee_ret(inner_evals + 2 * DIM, point_poly_eq, 2)

    copy_5(beta, postponed_point + n_vars * DIM)

    return fs5, postponed_point, new_claim_num, new_claim_den


@inline
def compute_stacked_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total_buf = Array(N_TABLES + 1)
    total_buf[0] = two_exp(log_memory + 1) + two_exp(log_bytecode_padded)  # memory + acc_memory + bytecode
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total_buf[table_index + 1] = total_buf[table_index] + n_rows * NUM_COLS_AIR[table_index]
    debug_assert(30 - 24 < MIN_LOG_N_ROWS_PER_TABLE)  # cf log2_ceil
    return MIN_LOG_N_ROWS_PER_TABLE + log2_ceil_runtime(total_buf[N_TABLES] / 2**MIN_LOG_N_ROWS_PER_TABLE)


def compute_total_gkr_n_vars(log_memory, log_bytecode_padded, tables_heights):
    total_buf = Array(N_TABLES + 1)
    total_buf[0] = two_exp(log_memory) + two_exp(log_bytecode_padded)
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        # +1 for the Multiplicity::Column bus, plus one block per Multiplicity::One bus.
        n_buses = len(ONE_BUSES_DOMSEPS[table_index]) + 1
        total_buf[table_index + 1] = total_buf[table_index] + n_rows * n_buses
    return log2_ceil_runtime(total_buf[N_TABLES])


def evaluate_air_constraints(table_index, inner_evals, air_alpha_powers, logup_alphas_eq_poly):
    res: Imm
    debug_assert(table_index < N_TABLES)
    match table_index:
        case 0:
            res = evaluate_air_constraints_table_0(inner_evals, air_alpha_powers, logup_alphas_eq_poly)
        case 1:
            res = evaluate_air_constraints_table_1(inner_evals, air_alpha_powers, logup_alphas_eq_poly)
        case 2:
            res = evaluate_air_constraints_table_2(inner_evals, air_alpha_powers, logup_alphas_eq_poly)
    return res


EVALUATE_AIR_FUNCTIONS_PLACEHOLDER
