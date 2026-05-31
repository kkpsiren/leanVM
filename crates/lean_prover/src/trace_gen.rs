use backend::*;
use lean_vm::*;
use std::collections::BTreeMap;
use utils::{ToUsize, get_poseidon_16_of_zero, transposed_par_iter_mut, transposed_par_iter_mut_slices};

#[derive(Debug)]
pub struct ExecutionTrace {
    pub traces: BTreeMap<Table, TableMatrix>,
    pub memory: Vec<F>, // of length a multiple of public_memory_size
    pub metadata: ExecutionMetadata,
}

const N_EXEC_COLUMNS: usize = N_TOTAL_EXECUTION_COLUMNS + N_TEMPORARY_EXEC_COLUMNS;

pub fn get_execution_trace(
    bytecode: &Bytecode,
    execution_result: ExecutionResult,
    min_table_log_n_rows: &BTreeMap<Table, usize>, // testing purpose
) -> ExecutionTrace {
    assert_eq!(execution_result.pcs.len(), execution_result.fps.len());

    let n_cycles = execution_result.pcs.len();
    let memory = &execution_result.memory;

    // Memory: replace `None` with zeros, then append the padding-row helpers.
    let mut memory_padded = memory.0.par_iter().map(|&v| v.unwrap_or(F::ZERO)).collect::<Vec<F>>();

    // Write [0000000000000000 | poseidon_compress(0000000000000000)] (to make lookups work on padding-rows).
    let padding_zero_vec_ptr = memory_padded.len();
    memory_padded.extend(std::iter::repeat_n(F::ZERO, 16));
    let null_poseidon_16_hash_ptr = memory_padded.len();
    memory_padded.extend_from_slice(get_poseidon_16_of_zero());

    // IMPORTANT: memory size should always be >= number of VM cycles
    let padded_memory_len = (memory_padded.len().max(n_cycles).max(1 << MIN_LOG_N_ROWS_PER_TABLE)).next_power_of_two();
    memory_padded.resize(padded_memory_len, F::ZERO);

    // --- Execution table: build directly into a column-major matrix (no per-column Vecs). ---
    let exec_floor = min_table_log_n_rows
        .get(&Table::execution())
        .copied()
        .unwrap_or_default()
        .max(MIN_LOG_N_ROWS_PER_TABLE);
    let exec_log_n_rows = log2_ceil_usize(n_cycles + 1).max(exec_floor);
    let exec_n_rows = 1 << exec_log_n_rows;
    let mut exec_data = F::zero_vec(N_EXEC_COLUMNS * exec_n_rows);
    {
        // Active rows [0, n_cycles): write each column's prefix in parallel, row-by-row.
        let mut active: [&mut [F]; N_EXEC_COLUMNS] = exec_data
            .chunks_mut(exec_n_rows)
            .map(|col| col.split_at_mut(n_cycles).0)
            .collect::<Vec<_>>()
            .try_into()
            .unwrap();

        transposed_par_iter_mut_slices(&mut active)
            .zip(execution_result.pcs.par_iter())
            .zip(execution_result.fps.par_iter())
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
    }
    // Padding rows [n_cycles, exec_n_rows): the execution padding row (self-loop at ending_pc).
    let exec_padding_row =
        Table::execution().padding_row(padding_zero_vec_ptr, null_poseidon_16_hash_ptr, bytecode.ending_pc);
    exec_data
        .par_chunks_mut(exec_n_rows)
        .zip(&exec_padding_row)
        .for_each(|(col, &pad)| col[n_cycles..].fill(pad));

    let ExecutionResult {
        mut traces, metadata, ..
    } = execution_result;
    // The execution table is built above; its builder entry (unused) is dropped here.
    traces.remove(&Table::execution());

    let poseidon_trace = traces.get_mut(&Table::poseidon16()).unwrap();
    fill_trace_poseidon_16(&mut poseidon_trace.columns);

    // Override the output columns the AIR leaves unconstrained with the actual memory values,
    // so the 16-cell output lookup matches. out_lo[4..8] is free when the output is only 4
    // elements (out4); out_hi is free for everything except the full 16-element
    // permutation
    {
        let split = POSEIDON_COL_OUT_LO + HALF_DIGEST_LEN;
        let (left, right) = poseidon_trace.columns.split_at_mut(split);
        let flag_out4_col = &left[POSEIDON_COL_FLAG_OUT4];
        let flag_out8_col = &left[POSEIDON_COL_FLAG_OUT8];
        let nu_c_col = &left[POSEIDON_COL_NU_C];
        const N: usize = HALF_DIGEST_LEN + DIGEST_LEN;
        let cols: &mut [Vec<F>; N] = (&mut right[..N]).try_into().unwrap();

        transposed_par_iter_mut(cols)
            .zip(flag_out4_col)
            .zip(flag_out8_col)
            .zip(nu_c_col)
            .for_each(|(((row, &flag_out4), &flag_out8), &nu_c)| {
                let base = nu_c.to_usize();
                if flag_out4 == F::ONE {
                    for j in 0..HALF_DIGEST_LEN {
                        *row[j] = memory_padded[base + HALF_DIGEST_LEN + j];
                    }
                }
                if flag_out8 == F::ONE || flag_out4 == F::ONE {
                    for j in 0..DIGEST_LEN {
                        *row[HALF_DIGEST_LEN + j] = memory_padded[base + DIGEST_LEN + j];
                    }
                }
            });
    }

    let extension_op_trace = traces.get_mut(&Table::extension_op()).unwrap();
    fill_trace_extension_op(extension_op_trace, &memory_padded);

    // Pad the precompile builders to a power of two, then transpose into column-major matrices.
    let mut matrices: BTreeMap<Table, TableMatrix> = BTreeMap::new();
    for table in traces.keys().copied().collect::<Vec<_>>() {
        let floor = min_table_log_n_rows
            .get(&table)
            .copied()
            .unwrap_or_default()
            .max(MIN_LOG_N_ROWS_PER_TABLE);
        pad_table(
            &table,
            &mut traces,
            padding_zero_vec_ptr,
            null_poseidon_16_hash_ptr,
            bytecode.ending_pc,
            floor,
        );
        let tt = &traces[&table];
        matrices.insert(
            table,
            TableMatrix::from_columns(&tt.columns, tt.non_padded_n_rows, tt.log_n_rows),
        );
    }

    matrices.insert(
        Table::execution(),
        TableMatrix {
            data: exec_data,
            n_rows: exec_n_rows,
            non_padded_n_rows: n_cycles,
            log_n_rows: exec_log_n_rows,
        },
    );

    ExecutionTrace {
        traces: matrices,
        memory: memory_padded,
        metadata,
    }
}

fn pad_table(
    table: &Table,
    traces: &mut BTreeMap<Table, TableTrace>,
    zero_vec_ptr: usize,
    null_poseidon_16_hash_ptr: usize,
    ending_pc: usize,
    min_log_n_rows: usize,
) {
    let trace = traces.get_mut(table).unwrap();
    let h = trace.columns[0].len();
    trace
        .columns
        .iter()
        .enumerate()
        .for_each(|(i, col)| assert_eq!(col.len(), h, "column {}, table {}", i, table.name()));

    trace.non_padded_n_rows = h;
    trace.log_n_rows = log2_ceil_usize(h + 1).max(min_log_n_rows);
    let n_rows = 1 << trace.log_n_rows;
    let padding_row = table.padding_row(zero_vec_ptr, null_poseidon_16_hash_ptr, ending_pc);
    trace.columns.par_iter_mut().enumerate().for_each(|(i, col)| {
        assert!(col.len() <= h); // potentially some columns have not been filled (in Poseidon -> we fill it later with SIMD + parallelism), but the first one should always be representative
        col.resize(n_rows, padding_row[i]);
    });
}
