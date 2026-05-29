use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use utils::{ToUsize, get_poseidon_16_of_zero, transposed_par_iter_mut_flat};

#[derive(Debug)]
pub struct ExecutionTrace {
    pub traces: BTreeMap<Table, TableTrace>,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
    pub metadata: ExecutionMetadata,
}

const N_EXEC_COLS: usize = N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS;

/// Padded (power-of-two) log-height of a table given its non-padded row count. Mirrors the former
/// `pad_table` rule: at least one padding row (`+1`), at least `MIN_LOG_N_ROWS_PER_TABLE`, and at
/// least any per-table floor requested for testing.
fn table_log_n_rows(non_padded: usize, table: &Table, min_table_log_n_rows: &BTreeMap<Table, usize>) -> usize {
    let floor = min_table_log_n_rows
        .get(table)
        .copied()
        .unwrap_or_default()
        .max(MIN_LOG_N_ROWS_PER_TABLE);
    log2_ceil_usize(non_padded + 1).max(floor)
}

pub fn get_execution_trace(
    bytecode: &Bytecode,
    execution_result: ExecutionResult,
    min_table_log_n_rows: &BTreeMap<Table, usize>, // testing purpose
) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());

    let n_cycles = execution_result.pcs.len();
    let ExecutionResult {
        mut traces,
        memory,
        metadata,
        pcs,
        fps,
        ..
    } = execution_result;

    // --- Padded memory + reserved padding pointers ---
    let mut memory_padded = memory.0.par_iter().map(|&v| v.unwrap_or(F::ZERO)).collect::<Vec<F>>();

    // Write [0000000000000000 | poseidon_compress(0000000000000000)] (to make lookups work on padding-rows).
    let padding_zero_vec_ptr = memory_padded.len();
    memory_padded.extend(std::iter::repeat_n(F::ZERO, 16));
    let null_poseidon_16_hash_ptr = memory_padded.len();
    memory_padded.extend_from_slice(get_poseidon_16_of_zero());

    // IMPORTANT: memory size should always be >= number of VM cycles
    let padded_memory_len = (memory_padded.len().max(n_cycles).max(1 << MIN_LOG_N_ROWS_PER_TABLE)).next_power_of_two();
    memory_padded.resize(padded_memory_len, F::ZERO);

    let ending_pc = bytecode.ending_pc;
    let mut out: BTreeMap<Table, TableTrace> = BTreeMap::new();

    // --- Execution table: built wholesale, directly into flat column-major storage ---
    {
        let table = Table::execution();
        let log_n_rows = table_log_n_rows(n_cycles, &table, min_table_log_n_rows);
        let padding_row = table.padding_row(padding_zero_vec_ptr, null_poseidon_16_hash_ptr, ending_pc);
        let mut exec = TableTrace::allocate_padded(n_cycles, log_n_rows, &padding_row);
        let n_rows = exec.n_rows;

        transposed_par_iter_mut_flat::<F, N_EXEC_COLS>(&mut exec.data, n_rows, n_cycles)
            .zip(pcs.par_iter())
            .zip(fps.par_iter())
            .for_each(|((trace_row, &pc), &fp)| {
                let instruction = &bytecode.code[pc].instruction;
                let field_repr = &bytecode.instructions_multilinear[pc * N_INSTRUCTION_COLUMNS.next_power_of_two()..]
                    [..N_INSTRUCTION_COLUMNS];

                let flag_a = field_repr[instr_idx(EXEC_COL_FLAG_A)];
                let flag_b = field_repr[instr_idx(EXEC_COL_FLAG_B)];
                let flag_c = field_repr[instr_idx(EXEC_COL_FLAG_C)];
                let flag_c_fp = field_repr[instr_idx(EXEC_COL_FLAG_C_FP)];
                let flag_ab_fp = field_repr[instr_idx(EXEC_COL_FLAG_AB_FP)];
                let aux_1 = field_repr[instr_idx(EXEC_COL_AUX_1)];
                let is_deref = aux_1 == F::TWO;

                let mut addr_a = F::ZERO;
                if flag_a.is_zero() && flag_ab_fp.is_zero() {
                    addr_a = F::from_usize(fp) + field_repr[instr_idx(EXEC_COL_OPERAND_A)];
                }
                let value_a = memory.0.get(addr_a.to_usize()).copied().flatten().unwrap_or_default();

                let mut addr_b = F::ZERO;
                if flag_b.is_zero() && flag_ab_fp.is_zero() {
                    addr_b = F::from_usize(fp) + field_repr[instr_idx(EXEC_COL_OPERAND_B)];
                } else if is_deref {
                    // DEREF: addr_B = value_A + operand_B
                    addr_b = value_a + field_repr[instr_idx(EXEC_COL_OPERAND_B)];
                }
                let value_b = memory.0.get(addr_b.to_usize()).copied().flatten().unwrap_or_default();

                let mut addr_c = F::ZERO;
                if flag_c.is_zero() && flag_c_fp.is_zero() {
                    addr_c = F::from_usize(fp) + field_repr[instr_idx(EXEC_COL_OPERAND_C)];
                }
                let value_c = memory.0.get(addr_c.to_usize()).copied().flatten().unwrap_or_default();

                for (j, field) in field_repr.iter().enumerate() {
                    *trace_row[j + N_RUNTIME_COLUMNS] = *field;
                }

                let nu_a = flag_a * field_repr[instr_idx(EXEC_COL_OPERAND_A)]
                    + (F::ONE - flag_a - flag_ab_fp) * value_a
                    + flag_ab_fp * (F::from_usize(fp) + field_repr[instr_idx(EXEC_COL_OPERAND_A)]);
                let nu_b = flag_b * field_repr[instr_idx(EXEC_COL_OPERAND_B)]
                    + (F::ONE - flag_b - flag_ab_fp) * value_b
                    + flag_ab_fp * (F::from_usize(fp) + field_repr[instr_idx(EXEC_COL_OPERAND_B)]);
                let nu_c = flag_c * field_repr[instr_idx(EXEC_COL_OPERAND_C)]
                    + (F::ONE - flag_c - flag_c_fp) * value_c
                    + flag_c_fp * (F::from_usize(fp) + field_repr[instr_idx(EXEC_COL_OPERAND_C)]);
                if let Instruction::Precompile(..) = instruction {
                    *trace_row[EXEC_COL_FLAG_PRECOMPILE] = F::ONE;
                }
                *trace_row[EXEC_COL_NU_A] = nu_a;
                *trace_row[EXEC_COL_NU_B] = nu_b;
                *trace_row[EXEC_COL_NU_C] = nu_c;

                *trace_row[EXEC_COL_VALUE_A] = value_a;
                *trace_row[EXEC_COL_VALUE_B] = value_b;
                *trace_row[EXEC_COL_VALUE_C] = value_c;
                *trace_row[EXEC_COL_PC] = F::from_usize(pc);
                *trace_row[EXEC_COL_FP] = F::from_usize(fp);
                *trace_row[EXEC_COL_ADDR_A] = addr_a;
                *trace_row[EXEC_COL_ADDR_B] = addr_b;
                *trace_row[EXEC_COL_ADDR_C] = addr_c;
            });

        out.insert(table, exec);
    }

    // --- Poseidon table: scatter the built columns, then fill round/output columns in place ---
    {
        let table = Table::poseidon16();
        let builder = traces.remove(&table).unwrap();
        let h = builder.n_rows;
        let log_n_rows = table_log_n_rows(h, &table, min_table_log_n_rows);
        let padding_row = table.padding_row(padding_zero_vec_ptr, null_poseidon_16_hash_ptr, ending_pc);
        let mut trace = TableTrace::allocate_padded(h, log_n_rows, &padding_row);
        scatter_builder(&mut trace, &builder, &table.built_columns(), h);

        fill_trace_poseidon_16(&mut trace, h);

        // For permute=0 rows, override unconstrained output columns with memory values so the
        // lookup matches. Same when half_output=1.
        poseidon_output_override(&mut trace, &memory_padded, h);

        out.insert(table, trace);
    }

    // --- Extension-op table: scatter the built columns, then fill v_A in place ---
    {
        let table = Table::extension_op();
        let builder = traces.remove(&table).unwrap();
        let h = builder.n_rows;
        let log_n_rows = table_log_n_rows(h, &table, min_table_log_n_rows);
        let padding_row = table.padding_row(padding_zero_vec_ptr, null_poseidon_16_hash_ptr, ending_pc);
        let mut trace = TableTrace::allocate_padded(h, log_n_rows, &padding_row);
        scatter_builder(&mut trace, &builder, &table.built_columns(), h);

        fill_trace_extension_op(&mut trace, &memory_padded);

        out.insert(table, trace);
    }

    ExecutionTrace {
        traces: out,
        memory: memory_padded,
        metadata,
    }
}

/// Transpose the row-major builder into the flat column-major trace: builder slot `s` (a column of
/// the row-major buffer) is gathered into flat column `built_cols[s]`, rows `[0, h)`. Columns not
/// listed in `built_cols` (e.g. Poseidon round/output columns) keep their padding value and are
/// computed in place by the subsequent fill pass.
fn scatter_builder(trace: &mut TableTrace, builder: &TableTraceBuilder, built_cols: &[ColIndex], h: usize) {
    debug_assert_eq!(built_cols.len(), builder.n_built);
    let n_built = builder.n_built;
    for (s, &final_c) in built_cols.iter().enumerate() {
        let col = trace.col_mut(final_c);
        for (r, cell) in col[..h].iter_mut().enumerate() {
            *cell = builder.data[r * n_built + s];
        }
    }
}

/// Override the upper half of `out_lo` (when `flag_short`) and all of `out_hi` with the memory
/// values for `permute == 0` rows, so the memory lookup matches. Operates on the active region
/// `[0, h)` of the flat trace; parallelised across the (few) output columns.
fn poseidon_output_override(trace: &mut TableTrace, memory_padded: &[F], h: usize) {
    let flag_short = trace.col(POSEIDON_COL_FLAG_SHORT)[..h].to_vec();
    let permute = trace.col(POSEIDON_COL_FLAG_PERMUTE)[..h].to_vec();
    let nu_c = trace.col(POSEIDON_COL_NU_C)[..h].to_vec();

    let split = POSEIDON_COL_OUT_LO + HALF_DIGEST_LEN;
    const N: usize = HALF_DIGEST_LEN + DIGEST_LEN;
    let n_rows = trace.n_rows;

    trace.data[split * n_rows..][..N * n_rows]
        .par_chunks_mut(n_rows)
        .enumerate()
        .for_each(|(jj, col)| {
            for i in 0..h {
                if permute[i] != F::ZERO {
                    continue;
                }
                let base = nu_c[i].to_usize();
                if jj < HALF_DIGEST_LEN {
                    if flag_short[i] == F::ONE {
                        col[i] = memory_padded[base + HALF_DIGEST_LEN + jj];
                    }
                } else {
                    col[i] = memory_padded[base + DIGEST_LEN + (jj - HALF_DIGEST_LEN)];
                }
            }
        });
}
