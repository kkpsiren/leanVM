from snark_lib import *
from whir import *
from hashing import *
from g8 import *

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
N_COLUMN_BUSES = N_COLUMN_BUSES_PLACEHOLDER  # [_; N_TABLES] — Multiplicity::Column buses per table (they precede the One buses)
COLUMN_BUS_PULL = COLUMN_BUS_PULL_PLACEHOLDER  # [[1 if Pull else 0; N_COLUMN_BUSES[t]]; N_TABLES]
COLUMN_BUS_OFFSETS = COLUMN_BUS_OFFSETS_PLACEHOLDER  # [_; N_TABLES] — prefix sums of N_COLUMN_BUSES
TOTAL_COLUMN_BUSES = TOTAL_COLUMN_BUSES_PLACEHOLDER
ONE_BUSES_DATA_COLS = ONE_BUSES_DATA_COLS_PLACEHOLDER  # [[[_; num_data]; num_buses]; N_TABLES]
ONE_BUSES_DATA_OFFSETS = ONE_BUSES_DATA_OFFSETS_PLACEHOLDER  # [[[_; num_data]; num_buses]; N_TABLES]
ONE_BUSES_NEW_COLS = ONE_BUSES_NEW_COLS_PLACEHOLDER  # [[[_; n_new]; num_buses]; N_TABLES]
ONE_BUS_RUNS = ONE_BUS_RUNS_PLACEHOLDER  # [[[start, n]; num_runs]; N_TABLES]: runs of consecutive single-column One buses (same domsep) verified in batch

NUM_COLS_AIR = NUM_COLS_AIR_PLACEHOLDER
MAX_NUM_COLS_AIR = MAX_NUM_COLS_AIR_PLACEHOLDER  # max(NUM_COLS_AIR[t] for t in 0..N_TABLES)
COLS_AIR_OFFSETS = COLS_AIR_OFFSETS_PLACEHOLDER  # prefix sums of NUM_COLS_AIR: the per-table base in the pcs arrays
TOTAL_NUM_COLS_AIR = TOTAL_NUM_COLS_AIR_PLACEHOLDER
ONE_BUSES_ALL_COLS = ONE_BUSES_ALL_COLS_PLACEHOLDER  # [[col, ...], _; N_TABLES] — sorted union of cols across all Multiplicity::One buses per table

MAX_AIR_FULL_DEGREE = MAX_AIR_FULL_DEGREE_PLACEHOLDER
N_AIR_COLUMNS = N_AIR_COLUMNS_PLACEHOLDER  # [_; N_TABLES]
N_AIR_SHIFT_COLUMNS = N_AIR_SHIFT_COLUMNS_PLACEHOLDER  # [_; N_TABLES] — by convention, shift column j of table t is column j
AIR_ALPHA_OFFSETS = AIR_ALPHA_OFFSETS_PLACEHOLDER  # [_; N_TABLES], # AIR_ALPHA_OFFSETS[t] = sum(N_AIR_CONSTRAINTS[k] for k in range(t))

N_INSTRUCTION_COLUMNS = N_INSTRUCTION_COLUMNS_PLACEHOLDER

LOG_GUEST_BYTECODE_LEN = LOG_GUEST_BYTECODE_LEN_PLACEHOLDER
EXEC_COL_PC = COL_PC_PLACEHOLDER
TOTAL_WHIR_STATEMENTS = TOTAL_WHIR_STATEMENTS_PLACEHOLDER
# Structural LogUp range sections (lean_vm::RANGE_SECTIONS): one region of 2^RANGE_LOG_TOTAL rows after the
# bytecode block, padded to the largest table height; section s has 2^RANGE_SECTION_LOG_ROWS[s] rows, is
# ALIVE (domainsep RANGE_SECTION_DOMSEPS[s]) for idx < 2^RANGE_SECTION_BITS[s] and DEAD above.
N_RANGE_SECTIONS = N_RANGE_SECTIONS_PLACEHOLDER
RANGE_LOG_TOTAL = RANGE_LOG_TOTAL_PLACEHOLDER
RANGE_MIN_LOG_ALIGN = RANGE_MIN_LOG_ALIGN_PLACEHOLDER
RANGE_SECTION_LOG_ROWS = RANGE_SECTION_LOG_ROWS_PLACEHOLDER  # [_; N_RANGE_SECTIONS]
RANGE_SECTION_BITS = RANGE_SECTION_BITS_PLACEHOLDER  # [_; N_RANGE_SECTIONS]
RANGE_SECTION_DOMSEPS = RANGE_SECTION_DOMSEPS_PLACEHOLDER  # [_; N_RANGE_SECTIONS]
RANGE_SECTION_DEAD_DOMSEPS = RANGE_SECTION_DEAD_DOMSEPS_PLACEHOLDER  # [_; N_RANGE_SECTIONS]
RANGE_SECTION_OFFSETS_DIV = RANGE_SECTION_OFFSETS_DIV_PLACEHOLDER  # [_; N_RANGE_SECTIONS]: offset within the region / 2^log_rows
STARTING_PC = STARTING_PC_PLACEHOLDER
ENDING_PC = ENDING_PC_PLACEHOLDER
BYTECODE_POINT_N_VARS = LOG_GUEST_BYTECODE_LEN + log2_ceil(N_INSTRUCTION_COLUMNS)
BYTECODE_ZERO_EVAL = BYTECODE_ZERO_EVAL_PLACEHOLDER
BYTECODE_CLAIM_SIZE = (BYTECODE_POINT_N_VARS + 1) * DIM
BYTECODE_CLAIM_SIZE_PADDED = next_multiple_of(BYTECODE_CLAIM_SIZE, DIGEST_LEN)
INNER_PUBLIC_MEMORY_LOG_SIZE = 3  # public input = 1 hash digest = 8 field elements
PUB_INPUT_SIZE = DIGEST_LEN  # the public input is a single digest
DIMS_N_CHUNKS = div_ceil(N_TABLES + 2, DIGEST_LEN)


def recursion(inner_public_memory, initial_fiat_shamir_cap):
    proof_transcript_size_buf = Array(1)
    hint_witness("proof_transcript_size", proof_transcript_size_buf)
    proof_transcript = Array(proof_transcript_size_buf[0])
    hint_witness("proof_transcript", proof_transcript)
    fs: Mut = fs_new(proof_transcript, initial_fiat_shamir_cap)

    fs = fs_observe(fs, inner_public_memory, PUB_INPUT_SIZE)  # observe public input (the data digest)

    # table dims: [whir_log_inv_rate, log_memory, log heights × N_TABLES], zero-padded to whole chunks
    fs, dims = fs_receive_chunks(fs, DIMS_N_CHUNKS)
    for i in unroll(N_TABLES + 2, DIMS_N_CHUNKS * DIGEST_LEN):
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

    log_bytecode_padded = maximum(maximum(LOG_GUEST_BYTECODE_LEN, log_max_table_height), RANGE_MIN_LOG_ALIGN)
    log_range_region = maximum(RANGE_LOG_TOTAL, log_max_table_height)
    assert RANGE_LOG_TOTAL <= log_memory

    stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode_padded, log_range_region, table_heights)
    assert stacked_n_vars <= TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - whir_log_inv_rate

    n_vars_logup_gkr = compute_total_gkr_n_vars(log_memory, log_bytecode_padded, log_range_region, table_heights)

    n_buses_per_table = Array(N_TABLES) # indexed by table_index
    n_cols_per_table = Array(N_TABLES) # indexed by table_index
    for i in unroll(0, N_TABLES):
        n_buses_per_table[i] = len(ONE_BUSES_DOMSEPS[i]) + N_COLUMN_BUSES[i] # Column buses (precompile bus, …) + One buses (memory / bytecode)
        n_cols_per_table[i] = NUM_COLS_AIR[i]

    gkr_table_base_offset = Array(N_TABLES)
    stacked_table_base_offset = Array(N_TABLES)
    gkr_cumul: Mut = two_exp(log_memory) + two_exp(log_bytecode_padded) + two_exp(log_range_region)
    stacked_cumul: Mut = two_exp(log_memory) * 2 + two_exp(log_bytecode_padded) + two_exp(log_range_region)
    for sorted_pos in unroll(0, N_TABLES):
        ti = sorted_tables[sorted_pos]
        gkr_table_base_offset[ti] = gkr_cumul
        stacked_table_base_offset[ti] = stacked_cumul
        n_rows = table_heights[ti]
        gkr_cumul += n_rows * n_buses_per_table[ti]
        stacked_cumul += n_rows * n_cols_per_table[ti]

    num_oods = get_num_oods(whir_log_inv_rate, stacked_n_vars)
    num_ood_at_commitment = num_oods[0]
    fs, whir_base_root, whir_base_ood_points, whir_base_ood_evals = parse_commitment(fs, num_ood_at_commitment)

    fs, logup_gamma = fs_sample_ef(fs)

    fs = fs_duplex(fs)
    fs, logup_beta = fs_sample_many_ef(fs, log2_ceil(MAX_BUS_WIDTH))

    logup_beta_eq_poly = compute_eq_mle_extension(logup_beta, log2_ceil(MAX_BUS_WIDTH))

    # LOGUP

    fs, quotient_gkr, point_gkr, numerators_value, denominators_value = verify_gkr_quotient(fs, n_vars_logup_gkr)
    set_to_5_zeros(quotient_gkr)

    memory_and_acc_prefix = multilinear_location_prefix(0, n_vars_logup_gkr - log_memory, point_gkr)

    fs, value_acc = fs_receive_ef_inlined(fs, 1)
    fs, value_memory = fs_receive_ef_inlined(fs, 1)

    retrieved_numerators_value: Mut = opposite_extension_ret(mul_extension_ret(memory_and_acc_prefix, value_acc))

    value_index = mle_of_01234567_etc(point_gkr + (n_vars_logup_gkr - log_memory) * DIM, log_memory)
    fingerprint_memory = fingerprint_2(LOGUP_MEMORY_DOMAINSEP, value_index, value_memory, logup_beta_eq_poly)
    retrieved_denominators_value: Mut = mul_extension_ret(
        memory_and_acc_prefix, sub_extension_ret(logup_gamma, fingerprint_memory)
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
        logup_beta + (log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)) * DIM,
        bytecode_claim + LOG_GUEST_BYTECODE_LEN * DIM,
        log2_ceil(N_INSTRUCTION_COLUMNS),
    )
    hint_witness("bytecode_value_hint", bytecode_claim + BYTECODE_POINT_N_VARS * DIM)
    for k in unroll(BYTECODE_CLAIM_SIZE, BYTECODE_CLAIM_SIZE_PADDED):
        bytecode_claim[k] = 0
    bytecode_value = bytecode_claim + BYTECODE_POINT_N_VARS * DIM
    bytecode_value_corrected: Mut = bytecode_value
    for i in unroll(0, log2_ceil(MAX_BUS_WIDTH) - log2_ceil(N_INSTRUCTION_COLUMNS)):
        bytecode_value_corrected = mul_extension_ret(
            bytecode_value_corrected, one_minus_self_extension_ret(logup_beta + i * DIM)
        )

    fs, value_bytecode_acc = fs_receive_ef_inlined(fs, 1)
    retrieved_numerators_value = sub_extension_ret(
        retrieved_numerators_value, mul_extension_ret(bytecode_multilinear_location_prefix, value_bytecode_acc)
    )

    bytecode_index_value = mle_of_01234567_etc(bytecode_and_acc_point, LOG_GUEST_BYTECODE_LEN)
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_multilinear_location_prefix,
            sub_extension_ret(
                logup_gamma,
                add_extension_ret(
                    bytecode_value_corrected,
                    add_extension_ret(
                        mul_extension_ret(bytecode_index_value, logup_beta_eq_poly + N_INSTRUCTION_COLUMNS * DIM),
                        mul_base_extension_ret(
                            LOGUP_BYTECODE_DOMAINSEP, logup_beta_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM
                        ),
                    ),
                ),
            ),
        ),
    )
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            bytecode_padded_multilinear_location_prefix,
            mle_of_zeros_then_ones_pow2(
                point_gkr + (n_vars_logup_gkr - log_bytecode_padded) * DIM,
                LOG_GUEST_BYTECODE_LEN,
                log_bytecode_padded,
            ),
        ),
    )

    # Range region: sections (numerator −acc, denominator gamma − fp(alive/dead domainsep, idx)), then padding.
    range_acc_values = Array(N_RANGE_SECTIONS * DIM)
    for s in unroll(0, N_RANGE_SECTIONS):
        sec_log = RANGE_SECTION_LOG_ROWS[s]
        sec_point = point_gkr + (n_vars_logup_gkr - sec_log) * DIM
        sec_prefix = multilinear_location_prefix(
            two_exp(log_memory - sec_log) + two_exp(log_bytecode_padded - sec_log) + RANGE_SECTION_OFFSETS_DIV[s],
            n_vars_logup_gkr - sec_log,
            point_gkr,
        )
        fs, sec_acc = fs_receive_ef_inlined(fs, 1)
        copy_ef(sec_acc, range_acc_values + s * DIM)
        retrieved_numerators_value = sub_extension_ret(retrieved_numerators_value, mul_extension_ret(sec_prefix, sec_acc))
        sec_idx = mle_of_01234567_etc(sec_point, sec_log)
        # alive iff the top (log_rows − bits) index bits are zero
        alive: Mut = embed_in_ef(1)
        for i in unroll(0, sec_log - RANGE_SECTION_BITS[s]):
            alive = mul_extension_ret(alive, one_minus_self_extension_ret(sec_point + i * DIM))
        sec_ds = sub_extension_ret(
            embed_in_ef(RANGE_SECTION_DEAD_DOMSEPS[s]),
            mul_base_extension_ret(RANGE_SECTION_DEAD_DOMSEPS[s] - RANGE_SECTION_DOMSEPS[s], alive),
        )
        sec_fp = add_extension_ret(
            mul_extension_ret(sec_idx, logup_beta_eq_poly),
            mul_extension_ret(sec_ds, logup_beta_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
        )
        retrieved_denominators_value = add_extension_ret(
            retrieved_denominators_value, mul_extension_ret(sec_prefix, sub_extension_ret(logup_gamma, sec_fp))
        )
    range_region_prefix = multilinear_location_prefix(
        two_exp(log_memory - log_range_region) + two_exp(log_bytecode_padded - log_range_region),
        n_vars_logup_gkr - log_range_region,
        point_gkr,
    )
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mul_extension_ret(
            range_region_prefix,
            mle_of_zeros_then_ones_pow2(
                point_gkr + (n_vars_logup_gkr - log_range_region) * DIM, RANGE_LOG_TOTAL, log_range_region
            ),
        ),
    )

    # Per-table data accumulators (indexed by table_index).
    bus_numerators_values = Array(TOTAL_COLUMN_BUSES * DIM)
    bus_denominators_values = Array(TOTAL_COLUMN_BUSES * DIM)
    pcs_inner_points = Array(N_TABLES)
    pcs_vals_logup = Array(TOTAL_NUM_COLS_AIR)
    pcs_vals_air = Array(TOTAL_NUM_COLS_AIR)
    pcs_shifts_air = Array(TOTAL_NUM_COLS_AIR)

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        offset: Mut = gkr_table_base_offset[table_index]

        inner_point = point_gkr + (n_vars_logup_gkr - log_n_rows) * DIM
        pcs_inner_points[table_index] = inner_point

        # The table's buses occupy consecutive n_rows-blocks of the GKR layout, so all their location
        # prefixes come from one eq-tensor (slot k = Column buses first, then One buses in order).
        n_bus_slots = N_COLUMN_BUSES[table_index] + len(ONE_BUSES_DOMSEPS[table_index])
        bus_prefixes = bus_slot_prefixes(offset / n_rows, n_vars_logup_gkr - log_n_rows, point_gkr, n_bus_slots)

        # Buses (data flow between tables — Multiplicity::Column), in bus order.
        for column_bus_idx in unroll(0, N_COLUMN_BUSES[table_index]):
            prefix = bus_prefixes + column_bus_idx * DIM

            fs, eval_on_selector = fs_receive_ef_inlined(fs, 1)
            retrieved_numerators_value = add_extension_ret(
                retrieved_numerators_value, mul_extension_ret(prefix, eval_on_selector)
            )

            fs, eval_on_data = fs_receive_ef_inlined(fs, 1)
            retrieved_denominators_value = add_extension_ret(
                retrieved_denominators_value, mul_extension_ret(prefix, eval_on_data)
            )

            bus_slot = COLUMN_BUS_OFFSETS[table_index] + column_bus_idx
            copy_ef(eval_on_selector, bus_numerators_values + bus_slot * DIM)
            copy_ef(eval_on_data, bus_denominators_values + bus_slot * DIM)

            offset += n_rows

        # Multiplicity::One buses (bytecode lookup + memory lookups + range pushes), in bus order.
        # A run of n >= 2 consecutive single-column buses with one domsep (the range pushes, thousands
        # per wide table) is verified in batch: one transcript read of n chunks (each [v | 0 0 0], the
        # same chunks the per-bus path would absorb one at a time), one tensor of location prefixes,
        # and three dot products — instead of a bit decomposition, a receive and a fingerprint per bus.
        for run_idx in unroll(0, len(ONE_BUS_RUNS[table_index])):
            run_start = ONE_BUS_RUNS[table_index][run_idx][0]
            run_n = ONE_BUS_RUNS[table_index][run_idx][1]
            if run_n == 1:
                one_bus_idx = run_start
                domsep = ONE_BUSES_DOMSEPS[table_index][one_bus_idx]
                n_new = len(ONE_BUSES_NEW_COLS[table_index][one_bus_idx])
                n_data = len(ONE_BUSES_DATA_COLS[table_index][one_bus_idx])

                if n_new != 0:  # a bus whose columns were all opened by earlier buses sends nothing
                    fs, new_evals = fs_receive_ef_inlined(fs, n_new)
                    for i in unroll(0, n_new):
                        new_col = ONE_BUSES_NEW_COLS[table_index][one_bus_idx][i]
                        pcs_vals_logup[COLS_AIR_OFFSETS[table_index] + new_col] = new_evals + i * DIM

                data_evals = Array(n_data * DIM)
                for i in unroll(0, n_data):
                    data_col = ONE_BUSES_DATA_COLS[table_index][one_bus_idx][i]
                    data_ofs = ONE_BUSES_DATA_OFFSETS[table_index][one_bus_idx][i]
                    src = pcs_vals_logup[COLS_AIR_OFFSETS[table_index] + data_col]
                    if data_ofs == 0:
                        copy_ef(src, data_evals + i * DIM)
                    if data_ofs != 0:
                        copy_ef(add_base_extension_ret(data_ofs, src), data_evals + i * DIM)

                pref = bus_prefixes + (N_COLUMN_BUSES[table_index] + one_bus_idx) * DIM
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, pref)
                fingerp = fingerprint_n(domsep, data_evals, n_data, logup_beta_eq_poly)
                retrieved_denominators_value = add_extension_ret(
                    retrieved_denominators_value,
                    mul_extension_ret(pref, sub_extension_ret(logup_gamma, fingerp)),
                )
                offset += n_rows
            if run_n != 1:
                domsep = ONE_BUSES_DOMSEPS[table_index][run_start]
                fs, chunks = fs_receive_chunks(fs, run_n)
                vals = Array(run_n * DIM)
                for i in unroll(0, run_n):
                    for j in unroll(DIM, DIGEST_LEN):
                        assert chunks[i * DIGEST_LEN + j] == 0
                    copy_ef(chunks + i * DIGEST_LEN, vals + i * DIM)
                    pcs_vals_logup[COLS_AIR_OFFSETS[table_index] + ONE_BUSES_NEW_COLS[table_index][run_start + i][0]] = vals + i * DIM
                prefixes = bus_prefixes + (N_COLUMN_BUSES[table_index] + run_start) * DIM
                s1 = sum_ef_long(prefixes, run_n)  # Σ_i prefix_i
                s2 = dot_product_ee_ret(prefixes, vals, run_n)  # Σ_i prefix_i · v_i
                # fingerprint_i = v_i·β[0] + domsep·β[top]  ⇒  Σ_i prefix_i·(γ − fingerprint_i) = (γ − domsep·β[top])·s1 − β[0]·s2
                gamma_minus_ds = sub_extension_ret(
                    logup_gamma, mul_base_extension_ret(domsep, logup_beta_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM)
                )
                retrieved_numerators_value = add_extension_ret(retrieved_numerators_value, s1)
                retrieved_denominators_value = add_extension_ret(
                    retrieved_denominators_value,
                    sub_extension_ret(mul_extension_ret(gamma_minus_ds, s1), mul_extension_ret(logup_beta_eq_poly, s2)),
                )
                offset += n_rows * run_n

    # Final logup adjustment (padding)
    retrieved_denominators_value = add_extension_ret(
        retrieved_denominators_value,
        mle_of_zeros_then_ones(point_gkr, gkr_cumul, n_vars_logup_gkr),
    )

    copy_ef(retrieved_numerators_value, numerators_value)
    copy_ef(retrieved_denominators_value, denominators_value)

    memory_and_acc_point = point_gkr + (n_vars_logup_gkr - log_memory) * DIM

    # END OF LOGUP

    # VERIFY BUS AND AIR — back-loaded batched sumcheck

    fs, air_alpha = fs_sample_ef(fs)
    air_alpha_powers = powers_const(air_alpha, TOTAL_NUM_AIR_CONSTRAINTS)

    initial_sum: Mut = ZERO_VEC_PTR
    for table_index in unroll(0, N_TABLES):
        alpha_offset = AIR_ALPHA_OFFSETS[table_index]
        # the j-th Column bus of the table owns alpha slots 2j (numerator, signed by direction) and 2j+1 (fingerprint)
        for column_bus_idx in unroll(0, N_COLUMN_BUSES[table_index]):
            bus_slot = COLUMN_BUS_OFFSETS[table_index] + column_bus_idx
            bus_numerator_value = bus_numerators_values + bus_slot * DIM
            bus_denominator_value = bus_denominators_values + bus_slot * DIM

            signed_numerator: Mut = bus_numerator_value
            if COLUMN_BUS_PULL[table_index][column_bus_idx] == 1:
                signed_numerator = opposite_extension_ret(signed_numerator)
            bus_final_value: Mut = mul_extension_ret(air_alpha_powers + (alpha_offset + 2 * column_bus_idx) * DIM, signed_numerator)
            bus_final_value = add_extension_ret(
                bus_final_value,
                mul_extension_ret(
                    air_alpha_powers + (alpha_offset + 2 * column_bus_idx + 1) * DIM,
                    sub_extension_ret(logup_gamma, bus_denominator_value),
                ),
            )
            initial_sum = add_extension_ret(initial_sum, bus_final_value)

    n_max = log_max_table_height
    # Batched AIR sumcheck:
    fs, all_challenges, batched_air_final_value = sumcheck_verify_reversed(fs, n_max, initial_sum, MAX_AIR_FULL_DEGREE)

    check_sum: Mut = ZERO_VEC_PTR
    air_evals_buf = Array(N_TABLES * DIM)
    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_flat_columns = N_AIR_COLUMNS[table_index]
        n_shift_columns = N_AIR_SHIFT_COLUMNS[table_index]
        alpha_offset = AIR_ALPHA_OFFSETS[table_index]

        fs, inner_evals = fs_receive_ef_inlined(fs, n_flat_columns + n_shift_columns)

        # written through an output buffer: a per-iteration return value would reuse one frame slot
        # across the unrolled iterations (compiler limitation), which is fatal in write-once memory
        evaluate_air_constraints_into(
            table_index, inner_evals, air_alpha_powers + alpha_offset * DIM, logup_beta_eq_poly, air_evals_buf + table_index * DIM
        )
        air_constraints_eval = air_evals_buf + table_index * DIM

        bus_point = pcs_inner_points[table_index]
        eq_val = poly_eq_extension_dynamic_ret(bus_point, all_challenges, log_n_rows)

        k_t = product_first_n(all_challenges + log_n_rows * DIM, n_max - log_n_rows)

        contribution = mul_extension_ret(k_t, mul_extension_ret(eq_val, air_constraints_eval))
        check_sum = add_extension_ret(check_sum, contribution)

        # AIR block (i=1): all flat cols 0..n_flat_columns populated; shifts 0..n_shift_columns populated.
        for i in unroll(0, n_flat_columns):
            pcs_vals_air[COLS_AIR_OFFSETS[table_index] + i] = inner_evals + i * DIM
        if n_shift_columns != 0:
            evals_shift = inner_evals + n_flat_columns * DIM
            for i in unroll(0, n_shift_columns):
                pcs_shifts_air[COLS_AIR_OFFSETS[table_index] + i] = evals_shift + i * DIM

    # verify that the AIR-batched sumcheck is valid
    copy_ef(check_sum, batched_air_final_value)

    fs, public_memory_random_point = fs_sample_many_ef(fs, INNER_PUBLIC_MEMORY_LOG_SIZE)
    poly_eq_public_mem = compute_eq_mle_extension(public_memory_random_point, INNER_PUBLIC_MEMORY_LOG_SIZE)
    public_memory_eval = Array(DIM)
    dot_product_be(inner_public_memory, poly_eq_public_mem, public_memory_eval, 2**INNER_PUBLIC_MEMORY_LOG_SIZE)

    # WHIR BASE
    fs = fs_duplex(fs)
    combination_randomness_gen: Mut
    fs, combination_randomness_gen = fs_sample_ef(fs)
    combination_randomness_powers: Mut = powers_runtime(
        combination_randomness_gen, num_ood_at_commitment + TOTAL_WHIR_STATEMENTS
    )
    whir_sum: Mut = Array(DIM)
    dot_product_ee_dynamic(whir_base_ood_evals, combination_randomness_powers, whir_sum, num_ood_at_commitment)
    curr_randomness: Mut = combination_randomness_powers + num_ood_at_commitment * DIM

    whir_sum = add_extension_ret(mul_extension_ret(value_memory, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_acc, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(public_memory_eval, curr_randomness), whir_sum)
    curr_randomness += DIM
    whir_sum = add_extension_ret(mul_extension_ret(value_bytecode_acc, curr_randomness), whir_sum)
    curr_randomness += DIM
    for s in unroll(0, N_RANGE_SECTIONS):
        whir_sum = add_extension_ret(mul_extension_ret(range_acc_values + s * DIM, curr_randomness), whir_sum)
        curr_randomness += DIM

    for table_index in unroll(0, N_TABLES):
        if table_index == EXECUTION_TABLE_INDEX:
            whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(STARTING_PC), curr_randomness), whir_sum)
            curr_randomness += DIM
            whir_sum = add_extension_ret(mul_extension_ret(embed_in_ef(ENDING_PC), curr_randomness), whir_sum)
            curr_randomness += DIM

        # LOGUP
        for k in unroll(0, len(ONE_BUSES_ALL_COLS[table_index])):
            col = ONE_BUSES_ALL_COLS[table_index][k]
            whir_sum = add_extension_ret(
                mul_extension_ret(pcs_vals_logup[COLS_AIR_OFFSETS[table_index] + col], curr_randomness),
                whir_sum,
            )
            curr_randomness += DIM

        # AIR
        for j in unroll(0, N_AIR_SHIFT_COLUMNS[table_index]):
            whir_sum = add_extension_ret(
                mul_extension_ret(pcs_shifts_air[COLS_AIR_OFFSETS[table_index] + j], curr_randomness),
                whir_sum,
            )
            curr_randomness += DIM
        for j in unroll(0, N_AIR_COLUMNS[table_index]):
            whir_sum = add_extension_ret(
                mul_extension_ret(pcs_vals_air[COLS_AIR_OFFSETS[table_index] + j], curr_randomness),
                whir_sum,
            )
            curr_randomness += DIM

    folding_randomness_global: Mut
    eval_weights: Mut
    final_value: Mut
    end_sum: Mut
    fs, folding_randomness_global, eval_weights, final_value, end_sum = whir_open(
        fs,
        stacked_n_vars,
        whir_log_inv_rate,
        whir_base_root,
        whir_base_ood_points,
        combination_randomness_powers,
        whir_sum,
    )

    curr_randomness = combination_randomness_powers + num_ood_at_commitment * DIM

    eq_memory_and_acc_point = poly_eq_extension_dynamic_ret(
        folding_randomness_global + (stacked_n_vars - log_memory) * DIM,
        memory_and_acc_point,
        log_memory,
    )
    prefix_memory = multilinear_location_prefix(0, stacked_n_vars - log_memory, folding_randomness_global)
    eval_weights = add_extension_ret(
        eval_weights,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_memory), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

    prefix_acc_memory = multilinear_location_prefix(1, stacked_n_vars - log_memory, folding_randomness_global)
    eval_weights = add_extension_ret(
        eval_weights,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_acc_memory), eq_memory_and_acc_point),
    )
    curr_randomness += DIM

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
    eval_weights = add_extension_ret(
        eval_weights,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_pub_mem), eq_pub_mem),
    )
    curr_randomness += DIM

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
    eval_weights = add_extension_ret(
        eval_weights,
        mul_extension_ret(mul_extension_ret(curr_randomness, prefix_bytecode_acc), eq_bytecode_acc),
    )
    curr_randomness += DIM

    for s in unroll(0, N_RANGE_SECTIONS):
        sec_log = RANGE_SECTION_LOG_ROWS[s]
        sec_point = point_gkr + (n_vars_logup_gkr - sec_log) * DIM
        eq_sec = Array(DIM)
        poly_eq_ee(folding_randomness_global + (stacked_n_vars - sec_log) * DIM, sec_point, eq_sec, sec_log)
        prefix_sec = multilinear_location_prefix(
            two_exp(log_memory + 1 - sec_log) + two_exp(log_bytecode_padded - sec_log) + RANGE_SECTION_OFFSETS_DIV[s],
            stacked_n_vars - sec_log,
            folding_randomness_global,
        )
        eval_weights = add_extension_ret(
            eval_weights, mul_extension_ret(mul_extension_ret(curr_randomness, prefix_sec), eq_sec)
        )
        curr_randomness += DIM

    for table_index in unroll(0, N_TABLES):
        log_n_rows = table_log_heights[table_index]
        n_rows = table_heights[table_index]
        total_num_cols = NUM_COLS_AIR[table_index]
        table_offset = stacked_table_base_offset[table_index]

        if table_index == EXECUTION_TABLE_INDEX:
            prefix_pc_start = multilinear_location_prefix(
                table_offset + EXEC_COL_PC * two_exp(log_n_cycles),
                stacked_n_vars,
                folding_randomness_global,
            )
            eval_weights = add_extension_ret(eval_weights, mul_extension_ret(curr_randomness, prefix_pc_start))
            curr_randomness += DIM

            prefix_pc_end = multilinear_location_prefix(
                table_offset + (EXEC_COL_PC + 1) * two_exp(log_n_cycles) - 1,
                stacked_n_vars,
                folding_randomness_global,
            )
            eval_weights = add_extension_ret(eval_weights, mul_extension_ret(curr_randomness, prefix_pc_end))
            curr_randomness += DIM

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
        logup_acc: Mut = ZERO_VEC_PTR
        for k in unroll(0, len(ONE_BUSES_ALL_COLS[table_index])):
            col = ONE_BUSES_ALL_COLS[table_index][k]
            prefix = column_prefixes + col * DIM
            logup_acc = add_extension_ret(logup_acc, mul_extension_ret(curr_randomness, prefix))
            curr_randomness += DIM
        eval_weights = add_extension_ret(eval_weights, mul_extension_ret(logup_acc, eq_factor_logup))

        # AIR
        if n_shift_columns != 0:
            next_factor = next_mle(all_challenges, inner_folding, log_n_rows)
            shift_sum = dot_product_ee_ret(curr_randomness, column_prefixes, n_shift_columns)
            eval_weights = add_extension_ret(eval_weights, mul_extension_ret(shift_sum, next_factor))
            curr_randomness += n_shift_columns * DIM
        eq_factor_air = poly_eq_extension_dynamic_ret(all_challenges, inner_folding, log_n_rows)
        air_sum = dot_product_ee_ret(curr_randomness, column_prefixes, N_AIR_COLUMNS[table_index])
        eval_weights = add_extension_ret(eval_weights, mul_extension_ret(air_sum, eq_factor_air))
        curr_randomness += N_AIR_COLUMNS[table_index] * DIM

    copy_ef(mul_extension_ret(eval_weights, final_value), end_sum)

    return bytecode_claim


def bus_slot_prefixes(first_slot, n_vars, point, n_slots: Const):
    # location prefixes of n_slots consecutive GKR slots starting at first_slot (one eq-tensor)
    if n_slots == 1:
        return multilinear_location_prefix(first_slot, n_vars, point)
    return compute_column_prefixes(first_slot, n_vars, point, n_slots)


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
    r: Mut = bits_first[n_vars - 1]
    for i in unroll(1, K):
        r += bits_first[n_vars - 1 - i] * 2**i

    # Column j lands at index r + j < 2^K + n_cols <= 2^(K+1).

    return column_prefixes + r * DIM


def fingerprint_2(table_index, data_1, data_2, logup_beta_eq_poly):
    buff = Array(DIM * 2)
    copy_ef(data_1, buff)
    copy_ef(data_2, buff + DIM)
    res: Mut = dot_product_ee_ret(buff, logup_beta_eq_poly, 2)
    res = add_extension_ret(
        res, mul_base_extension_ret(table_index, logup_beta_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM)
    )
    return res


@inline
def fingerprint_n(domsep, data_evals, n, logup_beta_eq_poly):
    res: Mut = dot_product_ee_ret(data_evals, logup_beta_eq_poly, n)
    res = add_extension_ret(
        res,
        mul_base_extension_ret(domsep, logup_beta_eq_poly + (2 ** log2_ceil(MAX_BUS_WIDTH) - 1) * DIM),
    )
    return res


def verify_gkr_quotient(prev_fs, n_vars):
    fs: Mut = prev_fs
    fs, nums = fs_receive_ef_inlined(fs, LOGUP_GKR_N_COEFFS_SENT)
    fs, denoms = fs_receive_ef_inlined(fs, LOGUP_GKR_N_COEFFS_SENT)

    initial_quotients = Array(LOGUP_GKR_N_COEFFS_SENT * DIM)
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT):
        div_extension(nums + k * DIM, denoms + k * DIM, initial_quotients + k * DIM)
    debug_assert(NUM_REPEATED_ONES <= LOGUP_GKR_N_COEFFS_SENT)
    debug_assert(LOGUP_GKR_N_COEFFS_SENT % NUM_REPEATED_ONES == 0)
    quotient: Mut = ZERO_VEC_PTR
    for k in unroll(0, LOGUP_GKR_N_COEFFS_SENT / NUM_REPEATED_ONES):
        quotient = add_extension_ret(
            quotient, sum_continuous_ef(initial_quotients + k * NUM_REPEATED_ONES * DIM, NUM_REPEATED_ONES)
        )

    points = Array(n_vars)
    claims_num = Array(n_vars)
    claims_den = Array(n_vars)

    fs, initial_point = fs_sample_many_ef(fs, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)
    points[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = initial_point

    point_poly_eq = compute_eq_mle_extension(initial_point, LOGUP_GKR_N_VARS_TO_SEND_COEFFS)

    first_claim_num = dot_product_ee_ret(nums, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    first_claim_den = dot_product_ee_ret(denoms, point_poly_eq, LOGUP_GKR_N_COEFFS_SENT)
    claims_num[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_num
    claims_den[LOGUP_GKR_N_VARS_TO_SEND_COEFFS - 1] = first_claim_den

    fs_buf = Array(n_vars - LOGUP_GKR_N_VARS_TO_SEND_COEFFS + 1)
    fs_buf[0] = fs
    for i in range(LOGUP_GKR_N_VARS_TO_SEND_COEFFS, n_vars):
        fs_buf[i - LOGUP_GKR_N_VARS_TO_SEND_COEFFS + 1], points[i], claims_num[i], claims_den[i] = verify_gkr_quotient_step(
            fs_buf[i - LOGUP_GKR_N_VARS_TO_SEND_COEFFS], i, points[i - 1], claims_num[i - 1], claims_den[i - 1]
        )
    fs = fs_buf[n_vars - LOGUP_GKR_N_VARS_TO_SEND_COEFFS]

    return (
        fs,
        quotient,
        points[n_vars - 1],
        claims_num[n_vars - 1],
        claims_den[n_vars - 1],
    )


def verify_gkr_quotient_step(prev_fs, n_vars, point, claim_num, claim_den):
    fs: Mut = prev_fs
    fs = fs_duplex(fs)
    fs, alpha = fs_sample_ef(fs)
    alpha_mul_claim_den = mul_extension_ret(alpha, claim_den)
    num_plus_alpha_mul_claim_den = add_extension_ret(claim_num, alpha_mul_claim_den)
    postponed_point = Array((n_vars + 1) * DIM)
    fs, postponed_value = sumcheck_verify_reversed_helper(
        fs, n_vars, num_plus_alpha_mul_claim_den, 3, postponed_point
    )
    fs, inner_evals = fs_receive_ef_inlined(fs, 4)
    a_num = inner_evals
    b_num = inner_evals + DIM
    a_den = inner_evals + 2 * DIM
    b_den = inner_evals + 3 * DIM
    sum_num, sum_den = sum_2_ef_fractions(a_num, a_den, b_num, b_den)
    sum_den_mul_alpha = mul_extension_ret(sum_den, alpha)
    sum_num_plus_sum_den_mul_alpha = add_extension_ret(sum_num, sum_den_mul_alpha)
    eq_factor = poly_eq_extension_dynamic_ret(point, postponed_point, n_vars)
    mul_extension(sum_num_plus_sum_den_mul_alpha, eq_factor, postponed_value)

    fs, beta = fs_sample_ef(fs)

    point_poly_eq = compute_eq_mle_extension(beta, 1)
    new_claim_num = dot_product_ee_ret(inner_evals, point_poly_eq, 2)
    new_claim_den = dot_product_ee_ret(inner_evals + 2 * DIM, point_poly_eq, 2)

    copy_ef(beta, postponed_point + n_vars * DIM)

    return fs, postponed_point, new_claim_num, new_claim_den


@inline
def compute_stacked_n_vars(log_memory, log_bytecode_padded, log_range_region, tables_heights):
    total: Mut = two_exp(log_memory + 1)  # memory + acc_memory
    total += two_exp(log_bytecode_padded)
    total += two_exp(log_range_region)  # range-section accs
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        total += n_rows * NUM_COLS_AIR[table_index]
    debug_assert(30 - 24 < MIN_LOG_N_ROWS_PER_TABLE)  # cf log2_ceil
    return MIN_LOG_N_ROWS_PER_TABLE + log2_ceil_runtime(total / 2**MIN_LOG_N_ROWS_PER_TABLE)


def compute_total_gkr_n_vars(log_memory, log_bytecode_padded, log_range_region, tables_heights):
    total: Mut = two_exp(log_memory)
    total += two_exp(log_bytecode_padded)
    total += two_exp(log_range_region)  # range region
    for table_index in unroll(0, N_TABLES):
        n_rows = tables_heights[table_index]
        # Column buses (precompile bus + routing/chunk/token buses) + one block per Multiplicity::One bus.
        n_buses = len(ONE_BUSES_DOMSEPS[table_index]) + N_COLUMN_BUSES[table_index]
        total += n_rows * n_buses
    return log2_ceil_runtime(total)


def evaluate_air_constraints_into(table_index, inner_evals, air_alpha_powers, logup_beta_eq_poly, out):
    res: Imm
    debug_assert(table_index < N_TABLES)
    match table_index:
        AIR_DISPATCH_ARMS_PLACEHOLDER
    copy_ef(res, out)
    return


EVALUATE_AIR_FUNCTIONS_PLACEHOLDER
