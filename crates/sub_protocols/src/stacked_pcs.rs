use backend::*;
use lean_vm::{
    ALL_TABLES, ColIndex, CommittedStatements, EXEC_COL_PC, MIN_LOG_MEMORY_SIZE, MIN_LOG_N_ROWS_PER_TABLE,
    N_INSTRUCTION_COLUMNS, STARTING_PC, sort_tables_by_height,
};
use lean_vm::{EF, F, Table, TableMatrix, TableT};
use std::collections::BTreeMap;
use utils::VarCount;
use utils::ansi::Colorize;

/*
Stacking of various (multilinear) polynomials into a single -big- (multilinear) polynomial, which is committed via WHIR.
[------------------------------ Memory ------------------------------]
[------------------------ Memory Accumulator ------------------------]
[------ Bytecode Accumulator -----]                             (padded to bas as least as large as the execution table)
[-------- Execution Col 0 --------]
[-------- Execution Col 1 --------]
...
[-------- Execution Col 19 -------]
[Dot-Product Col 0]
[Dot-Product Col 1]
...
[Dot-Product Col n]
[Poseidon-16 Col 0]
[Poseidon-16 Col 1]
...
[Poseidon-16 Col m]

(The order between Dot-Product and Poseidon-16 varies based on which table has more rows, but they are always after the execution table)
*/

/// Offsets and size of the stacked polynomial layout. Single source of truth, shared by the
/// committed-statement construction, the segmented-view builder, and `compute_stacked_n_vars`.
#[derive(Debug)]
pub struct StackedLayout {
    pub stacked_n_vars: VarCount,
    /// End of the last segment (the rest, up to `1 << stacked_n_vars`, is zero padding).
    pub active_len: usize,
    /// Element offset of each table's first committed column.
    pub table_offsets: BTreeMap<Table, usize>,
}

pub fn stacked_layout(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
) -> StackedLayout {
    let tables_heights_sorted = sort_tables_by_height(tables_log_heights);
    let max_table_n_vars = tables_heights_sorted[0].1;
    let mut offset = (2 << log_memory) + (1 << log_bytecode.max(max_table_n_vars));
    let mut table_offsets = BTreeMap::new();
    for (table, n_vars) in &tables_heights_sorted {
        table_offsets.insert(*table, offset);
        offset += table.n_columns() << n_vars;
    }
    StackedLayout {
        stacked_n_vars: log2_ceil_usize(offset),
        active_len: offset,
        table_offsets,
    }
}

/// Build the segmented view of the stacked polynomial over the prover's witness pieces,
/// without materializing it. The segment order/offsets match the committed layout exactly.
pub fn build_stacked_poly<'a>(
    memory: &'a [F],
    memory_acc: &'a [F],
    bytecode_acc: &'a [F],
    traces: &'a BTreeMap<Table, TableMatrix>,
) -> StackedPoly<'a, EF> {
    assert_eq!(memory.len(), memory_acc.len());
    let log_memory = log2_strict_usize(memory.len());
    let log_bytecode = log2_strict_usize(bytecode_acc.len());
    let tables_log_heights: BTreeMap<Table, VarCount> =
        traces.iter().map(|(table, m)| (*table, m.log_n_rows)).collect();
    // Memory must be at least as large as the largest table.
    assert!(log_memory >= *tables_log_heights.values().max().unwrap());

    let layout = stacked_layout(log_memory, log_bytecode, &tables_log_heights);

    let mut segments = vec![
        StackedSegment {
            offset: 0,
            data: memory,
            log_block: log_memory,
        },
        StackedSegment {
            offset: 1 << log_memory,
            data: memory_acc,
            log_block: log_memory,
        },
        StackedSegment {
            offset: 2 << log_memory,
            data: bytecode_acc,
            log_block: log_bytecode,
        },
    ];
    for (table, &offset) in &layout.table_offsets {
        let m = &traces[table];
        segments.push(StackedSegment {
            offset,
            data: m.committed_segment(table.n_columns()),
            log_block: m.log_n_rows,
        });
    }

    tracing::info!(
        "{}",
        format!(
            "stacked PCS data: {} = 2^{} * (1 + {:.2})",
            layout.active_len,
            layout.stacked_n_vars - 1,
            (layout.active_len as f64) / (1 << (layout.stacked_n_vars - 1)) as f64 - 1.0
        )
        .green()
    );

    StackedPoly::new(layout.stacked_n_vars, segments)
}

pub fn stacked_pcs_global_statements(
    stacked_n_vars: VarCount,
    memory_n_vars: VarCount,
    bytecode_n_vars: VarCount,
    ending_pc: usize,
    previous_statements: Vec<SparseStatement<EF>>,
    tables_heights: &BTreeMap<Table, VarCount>,
    committed_statements: &CommittedStatements,
) -> Vec<SparseStatement<EF>> {
    assert_eq!(tables_heights.len(), committed_statements.len());

    let table_offsets = stacked_layout(memory_n_vars, bytecode_n_vars, tables_heights).table_offsets;

    let mut global_statements = previous_statements;
    for table in ALL_TABLES {
        let n_vars = tables_heights[&table];
        let offset = table_offsets[&table];
        if table.is_execution_table() {
            // Important: ensure both initial and final PC conditions are correct
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + (EXEC_COL_PC << n_vars),
                EF::from_usize(STARTING_PC),
            ));
            global_statements.push(SparseStatement::unique_value(
                stacked_n_vars,
                offset + ((EXEC_COL_PC + 1) << n_vars) - 1,
                EF::from_usize(ending_pc),
            ));
        }
        for (point, eq_values, next_values) in &committed_statements[&table] {
            if !next_values.is_empty() {
                global_statements.push(SparseStatement::new_next(
                    stacked_n_vars,
                    point.clone(),
                    next_values
                        .iter()
                        .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                        .collect(),
                ));
            }
            global_statements.push(SparseStatement::new(
                stacked_n_vars,
                point.clone(),
                eq_values
                    .iter()
                    .map(|(&col_index, &value)| SparseValue::new((offset >> n_vars) + col_index, value))
                    .collect(),
            ));
        }
    }
    global_statements
}

pub fn stacked_pcs_parse_commitment(
    whir_config_builder: &WhirConfigBuilder,
    verifier_state: &mut impl FSVerifier<EF>,
    log_memory: usize,
    log_bytecode: usize,
    tables_heights: &BTreeMap<Table, VarCount>,
) -> Result<ParsedCommitment<F, EF>, ProofError> {
    if log_memory < *tables_heights.values().max().unwrap() {
        // memory must be at least as large as the largest table
        return Err(ProofError::InvalidProof);
    }

    let stacked_n_vars = compute_stacked_n_vars(log_memory, log_bytecode, tables_heights);
    if stacked_n_vars
        > F::TWO_ADICITY + whir_config_builder.folding_factor.at_round(0) - whir_config_builder.starting_log_inv_rate
    {
        return Err(ProofError::InvalidProof);
    }
    WhirConfig::new(whir_config_builder, stacked_n_vars).parse_commitment(verifier_state)
}

fn compute_stacked_n_vars(
    log_memory: usize,
    log_bytecode: usize,
    tables_log_heights: &BTreeMap<Table, VarCount>,
) -> VarCount {
    stacked_layout(log_memory, log_bytecode, tables_log_heights).stacked_n_vars
}

pub fn min_stacked_n_vars(log_bytecode: usize) -> usize {
    let mut min_tables_log_heights = BTreeMap::new();
    for table in ALL_TABLES {
        min_tables_log_heights.insert(table, MIN_LOG_N_ROWS_PER_TABLE);
    }
    compute_stacked_n_vars(MIN_LOG_MEMORY_SIZE, log_bytecode, &min_tables_log_heights)
}

pub fn total_whir_statements() -> usize {
    6 // memory + memory_acc + public_memory + bytecode_acc + pc_start + pc_end
     + ALL_TABLES
        .iter()
        .map(|table| {
            let mut seen_cols = std::collections::HashSet::<ColIndex>::new();
            for bus in table.bus_interactions().iter().filter(|b| b.is_memory_lookup()) {
                for entry in &bus.data {
                    if let Some(col) = entry.column() {
                        seen_cols.insert(col);
                    }
                }
            }
            table.n_columns() + table.n_shift_columns() + seen_cols.len()
        })
        .sum::<usize>()
        // bytecode lookup
        + 1 // PC
        + N_INSTRUCTION_COLUMNS
}
