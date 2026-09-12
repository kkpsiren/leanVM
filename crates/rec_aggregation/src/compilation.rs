use backend::*;
use backend::{G8_N_CONSTRAINTS, SymbolicG8Identity};
use lean_compiler::{CompilationFlags, ProgramSource, compile_program_with_flags};
use lean_prover::{
    GRINDING_BITS, MAX_NUM_VARIABLES_TO_SEND_COEFFS, RS_DOMAIN_INITIAL_REDUCTION_FACTOR, WHIR_INITIAL_FOLDING_FACTOR,
    WHIR_SUBSEQUENT_FOLDING_FACTOR, default_whir_config,
};
use lean_vm::*;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::OnceLock;
use sub_protocols::{N_VARS_TO_SEND_GKR_COEFFS, min_stacked_n_vars, total_whir_statements};
use tracing::instrument;
use xmss::{LOG_LIFETIME, PUBLIC_PARAM_LEN_FE, RANDOMNESS_LEN_FE, TARGET_SUM, V, W, XMSS_DIGEST_LEN};

use crate::bytecode_claims::bytecode_reduction_sumcheck_proof_size;
use crate::single_message_aggregation::TWEAK_TABLE_SIZE_FE_PADDED;

// preamble memory layout: see `build_preamble_memory` in utils.py:
// [000.. (ZERO_VEC_LEN)][10000000 (fiat-shamir domain sep)][10000 (one in extension field)][111... (NUM_REPEATED_ONES)][tweak table]
pub const ZERO_VEC_LEN: usize = 16;
pub const NUM_REPEATED_ONES: usize = 32;
pub const PREAMBLE_MEMORY_LEN: usize =
    ZERO_VEC_LEN + DIGEST_LEN + DIMENSION + NUM_REPEATED_ONES + TWEAK_TABLE_SIZE_FE_PADDED;

pub(crate) const MERKLE_LEVELS_PER_CHUNK_FOR_SLOT: usize = 4;
pub(crate) const N_MERKLE_CHUNKS_FOR_SLOT: usize = LOG_LIFETIME / MERKLE_LEVELS_PER_CHUNK_FOR_SLOT;

static BYTECODE: OnceLock<Bytecode> = OnceLock::new();
static VERIFIER_BYTECODE: OnceLock<DictionaryProgram> = OnceLock::new();

pub fn try_get_aggregation_verifier_program() -> Option<&'static dyn VerifierProgram> {
    VERIFIER_BYTECODE.get().map(|p| p as &dyn VerifierProgram)
        .or_else(|| try_get_aggregation_bytecode().map(|p| p as &dyn VerifierProgram))
}

pub fn get_aggregation_verifier_program() -> &'static dyn VerifierProgram {
    try_get_aggregation_verifier_program().expect("initialize the aggregation program first")
}

pub fn get_aggregation_bytecode() -> &'static Bytecode {
    BYTECODE
        .get()
        .unwrap_or_else(|| panic!("call init_aggregation_bytecode() first"))
}

pub fn try_get_aggregation_bytecode() -> Option<&'static Bytecode> {
    BYTECODE.get()
}

pub fn init_aggregation_bytecode() {
    BYTECODE.get_or_init(compile_main_program_self_referential);
}

/// Load only an explicitly prepared, authenticated release prover cache. No implicit compilation.
pub fn init_aggregation_bytecode_cached(cache_dir: &std::path::Path) -> bool {
    if BYTECODE.get().is_some() { return true; }
    let bytes = read_cache_bounded(&cache_dir.join(crate::prover_artifact::PROVER_CACHE_FILENAME))
        .expect("prepare and audit the release prover cache explicitly before proving");
    let bytecode = crate::prover_artifact::load_prover_cache(&bytes)
        .expect("prover cache must match the release pin");
    BYTECODE.set(bytecode).unwrap_or_else(|_| panic!("bytecode already initialized"));
    true
}

fn read_cache_bounded(path: &std::path::Path) -> std::io::Result<Vec<u8>> {
    use std::io::Read;
    let mut bytes = Vec::new();
    std::fs::File::open(path)?.take(crate::prover_artifact::MAX_PROVER_CACHE_BYTES as u64 + 1)
        .read_to_end(&mut bytes)?;
    if bytes.len() > crate::prover_artifact::MAX_PROVER_CACHE_BYTES {
        return Err(std::io::Error::new(std::io::ErrorKind::InvalidData, "prover cache exceeds limit"));
    }
    Ok(bytes)
}

/// Portable release loader: only the authenticated dictionary artifact is accepted.
/// Independent table linkage is checked by the standalone rehash-verifier-artifact command.
pub fn init_aggregation_bytecode_pinned(bytes: &[u8], expected_hash: [u32; 8]) -> Result<(), String> {
    if try_get_aggregation_verifier_program().is_some() { return Err("bytecode already initialized".into()); }
    if expected_hash != crate::verifier_artifact::VK_HASH { return Err("unsupported release pin".into()); }
    let program = DictionaryProgram::from_pinned_bytes(bytes, &crate::verifier_artifact::ARTIFACT_SHA512, expected_hash)?;
    VERIFIER_BYTECODE.set(program).map_err(|_| "bytecode already initialized".into())
}

static EMBEDDED_ZK_DSL: include_dir::Dir<'_> = include_dir::include_dir!("$CARGO_MANIFEST_DIR/zkdsl_implem");

pub const MAX_RECURSIONS: usize = 16;
pub const MAX_XMSS_AGGREGATED: usize = 1 << 15; // TODO increase (we would need a bigger minimal memory size, totally doable)
pub const MAX_XMSS_DUPLICATES: usize = 1 << 15; // ...same

pub(crate) const SINGLE_MESSAGE_FLAG: usize = 1;
pub(crate) const MULTI_MESSAGE_FLAG: usize = 0;
pub(crate) const ED25519_LEAF_FLAG: usize = 2;
pub(crate) const ED25519_NODE_FLAG: usize = 3; // a node over K child proofs (leaves or nodes)

pub(crate) const BYTECODE_CLAIM_OFFSET: usize = DIGEST_LEN;
/// Single-message component data: pubkeys_hash | message | merkle_chunks | tweaks_hash.
pub(crate) const COMPONENT_DATA_SIZE: usize = DIGEST_LEN + DIGEST_LEN + N_MERKLE_CHUNKS_FOR_SLOT + DIGEST_LEN; // pubkeys_hash + hashed message + merkle chunks + tweaks_hash

pub(crate) fn bytecode_claim_size_padded(program_log_size: usize) -> usize {
    let bytecode_point_n_vars = program_log_size + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    ((bytecode_point_n_vars + 1) * DIMENSION).next_multiple_of(DIGEST_LEN)
}

pub(crate) fn initial_fiat_shamir_cap_offset(program_log_size: usize) -> usize {
    BYTECODE_CLAIM_OFFSET + bytecode_claim_size_padded(program_log_size)
}

pub(crate) fn component_data_offset(program_log_size: usize) -> usize {
    initial_fiat_shamir_cap_offset(program_log_size) + DIGEST_LEN
}

pub(crate) fn single_message_input_data_size_padded(program_log_size: usize) -> usize {
    component_data_offset(program_log_size) + COMPONENT_DATA_SIZE
}

fn compile_main_program(program_log_size: usize, bytecode_zero_eval: F) -> Bytecode {
    let replacements = build_replacements(program_log_size, bytecode_zero_eval);

    let source = ProgramSource::Embedded {
        entry: "main.py".to_string(),
        dir: &EMBEDDED_ZK_DSL,
    };
    compile_program_with_flags(&source, CompilationFlags { replacements })
}

#[instrument(skip_all)]
fn compile_main_program_self_referential() -> Bytecode {
    // The fixed point is 2^20 today; starting there saves one full compile (≈ 29 s) per process.
    // FB_BYTECODE_LOG_SIZE overrides the first guess (the loop still converges to the true size).
    let mut log_size_guess = std::env::var("FB_BYTECODE_LOG_SIZE").ok().and_then(|v| v.parse().ok()).unwrap_or(20);
    let bytecode_zero_eval = F::ZERO;
    for _ in 0..10 {
        let bytecode = compile_main_program(log_size_guess, bytecode_zero_eval);
        let actual_log_size = bytecode.log_size();
        assert_eq!(bytecode.ending_pc(), (1 << actual_log_size) - 1);
        assert_eq!(bytecode_zero_eval, bytecode.instructions_multilinear()[0]);
        if actual_log_size == log_size_guess {
            return bytecode;
        }
        eprintln!(
            "Wrong guess at `compile_main_program_self_referential` (log_size {log_size_guess}->{actual_log_size})"
        );
        log_size_guess = actual_log_size;
    }
    panic!("`compile_main_program_self_referential` did not converge");
}

fn build_replacements(log_inner_bytecode: usize, bytecode_zero_eval: F) -> BTreeMap<String, String> {
    let ending_pc = (1 << log_inner_bytecode) - 1;
    let min_stacked = min_stacked_n_vars(log_inner_bytecode);

    let mut replacements = BTreeMap::new();

    let mut all_potential_num_queries = vec![];
    let mut all_potential_query_grinding = vec![];
    let mut all_potential_num_oods = vec![];
    let mut all_potential_folding_grinding = vec![];
    let mut too_much_grinding = false;
    for log_inv_rate in MIN_WHIR_LOG_INV_RATE..=MAX_WHIR_LOG_INV_RATE {
        let max_n_vars = F::TWO_ADICITY + WHIR_INITIAL_FOLDING_FACTOR - log_inv_rate;
        let whir_config_builder = default_whir_config(log_inv_rate);

        let mut queries_for_rate = vec![];
        let mut query_grinding_for_rate = vec![];
        let mut oods_for_rate = vec![];
        let mut folding_grinding_for_rate = vec![];
        for n_vars in min_stacked..=max_n_vars {
            let cfg = WhirConfig::<EF>::new(&whir_config_builder, n_vars);
            if cfg.max_folding_pow_bits() > GRINDING_BITS {
                too_much_grinding = true;
            }

            let mut num_queries = vec![];
            let mut query_grinding_bits = vec![];
            let mut oods = vec![cfg.commitment_ood_samples];
            let mut folding_grinding = vec![cfg.starting_folding_pow_bits];
            for round in &cfg.round_parameters {
                num_queries.push(round.num_queries);
                query_grinding_bits.push(round.query_pow_bits);
                oods.push(round.ood_samples);
                folding_grinding.push(round.folding_pow_bits);
            }
            num_queries.push(cfg.final_queries);
            query_grinding_bits.push(cfg.final_query_pow_bits);

            queries_for_rate.push(format!(
                "[{}]",
                num_queries.iter().map(|q| q.to_string()).collect::<Vec<_>>().join(", ")
            ));
            query_grinding_for_rate.push(format!(
                "[{}]",
                query_grinding_bits
                    .iter()
                    .map(|q| q.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
            oods_for_rate.push(format!(
                "[{}]",
                oods.iter().map(|o| o.to_string()).collect::<Vec<_>>().join(", ")
            ));
            folding_grinding_for_rate.push(format!(
                "[{}]",
                folding_grinding
                    .iter()
                    .map(|g| g.to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
        all_potential_num_queries.push(format!("[{}]", queries_for_rate.join(", ")));
        all_potential_query_grinding.push(format!("[{}]", query_grinding_for_rate.join(", ")));
        all_potential_num_oods.push(format!("[{}]", oods_for_rate.join(", ")));
        all_potential_folding_grinding.push(format!("[{}]", folding_grinding_for_rate.join(", ")));
    }
    if too_much_grinding {
        tracing::info!("Warning: Too much grinding for WHIR folding"); // TODO
    }
    replacements.insert(
        "WHIR_FIRST_RS_REDUCTION_FACTOR_PLACEHOLDER".to_string(),
        RS_DOMAIN_INITIAL_REDUCTION_FACTOR.to_string(),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_QUERIES_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_queries.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_QUERY_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_query_grinding.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_NUM_OODS_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_num_oods.join(", ")),
    );
    replacements.insert(
        "WHIR_ALL_POTENTIAL_FOLDING_GRINDING_PLACEHOLDER".to_string(),
        format!("[{}]", all_potential_folding_grinding.join(", ")),
    );
    replacements.insert("MIN_STACKED_N_VARS_PLACEHOLDER".to_string(), min_stacked.to_string());

    // VM recursion parameters (different from WHIR)
    replacements.insert("N_TABLES_PLACEHOLDER".to_string(), N_TABLES.to_string());
    replacements.insert(
        "MIN_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        MIN_LOG_N_ROWS_PER_TABLE.to_string(),
    );
    let mut max_log_n_rows_per_table = MAX_LOG_N_ROWS_PER_TABLE.to_vec();
    max_log_n_rows_per_table.sort_by_key(|(table, _)| table.index());
    max_log_n_rows_per_table.dedup();
    assert_eq!(max_log_n_rows_per_table.len(), N_TABLES);
    replacements.insert(
        "MIN_WHIR_LOG_INV_RATE_PLACEHOLDER".to_string(),
        MIN_WHIR_LOG_INV_RATE.to_string(),
    );
    replacements.insert(
        "MAX_WHIR_LOG_INV_RATE_PLACEHOLDER".to_string(),
        MAX_WHIR_LOG_INV_RATE.to_string(),
    );
    replacements.insert(
        "MAX_NUM_VARIABLES_TO_SEND_COEFFS_PLACEHOLDER".to_string(),
        MAX_NUM_VARIABLES_TO_SEND_COEFFS.to_string(),
    );
    replacements.insert(
        "LOGUP_GKR_N_VARS_TO_SEND_COEFFS_PLACEHOLDER".to_string(),
        N_VARS_TO_SEND_GKR_COEFFS.to_string(),
    );
    replacements.insert(
        "WHIR_INITIAL_FOLDING_FACTOR_PLACEHOLDER".to_string(),
        WHIR_INITIAL_FOLDING_FACTOR.to_string(),
    );
    replacements.insert(
        "WHIR_SUBSEQUENT_FOLDING_FACTOR_PLACEHOLDER".to_string(),
        WHIR_SUBSEQUENT_FOLDING_FACTOR.to_string(),
    );
    replacements.insert(
        "MAX_LOG_N_ROWS_PER_TABLE_PLACEHOLDER".to_string(),
        format!(
            "[{}]",
            max_log_n_rows_per_table
                .iter()
                .map(|(_, v)| v.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        ),
    );
    replacements.insert(
        "MIN_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MIN_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_LOG_MEMORY_SIZE_PLACEHOLDER".to_string(),
        MAX_LOG_MEMORY_SIZE.to_string(),
    );
    replacements.insert(
        "MAX_BUS_WIDTH_PLACEHOLDER".to_string(),
        (1 << LOG_MAX_BUS_WIDTH).to_string(),
    );
    replacements.insert(
        "LOGUP_MEMORY_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_MEMORY_DOMAINSEP.to_string(),
    );
    {
        use lean_vm::{N_RANGE_SECTIONS, RANGE_LOG_TOTAL, RANGE_MIN_LOG_ALIGN, RANGE_SECTIONS};
        let list = |f: &dyn Fn(usize) -> usize| format!("[{}]", (0..N_RANGE_SECTIONS).map(|s| f(s).to_string()).collect::<Vec<_>>().join(", "));
        let offsets_div: Vec<usize> = { let mut off = 0; RANGE_SECTIONS.iter().map(|sec| { let d = off >> sec.log_rows; off += 1 << sec.log_rows; d }).collect() };
        replacements.insert("N_RANGE_SECTIONS_PLACEHOLDER".to_string(), N_RANGE_SECTIONS.to_string());
        replacements.insert("RANGE_LOG_TOTAL_PLACEHOLDER".to_string(), RANGE_LOG_TOTAL.to_string());
        replacements.insert("RANGE_MIN_LOG_ALIGN_PLACEHOLDER".to_string(), RANGE_MIN_LOG_ALIGN.to_string());
        replacements.insert("RANGE_SECTION_LOG_ROWS_PLACEHOLDER".to_string(), list(&|s| RANGE_SECTIONS[s].log_rows));
        replacements.insert("RANGE_SECTION_BITS_PLACEHOLDER".to_string(), list(&|s| RANGE_SECTIONS[s].bits));
        replacements.insert("RANGE_SECTION_DOMSEPS_PLACEHOLDER".to_string(), list(&|s| RANGE_SECTIONS[s].domainsep));
        replacements.insert("RANGE_SECTION_DEAD_DOMSEPS_PLACEHOLDER".to_string(), list(&|s| RANGE_SECTIONS[s].dead_domainsep));
        replacements.insert("RANGE_SECTION_OFFSETS_DIV_PLACEHOLDER".to_string(), list(&|s| offsets_div[s]));
    }
    replacements.insert(
        "LOGUP_BYTECODE_DOMAINSEP_PLACEHOLDER".to_string(),
        LOGUP_BYTECODE_DOMAINSEP.to_string(),
    );
    replacements.insert(
        "LOG_GUEST_BYTECODE_LEN_PLACEHOLDER".to_string(),
        log_inner_bytecode.to_string(),
    );
    replacements.insert("COL_PC_PLACEHOLDER".to_string(), EXEC_COL_PC.to_string());
    let bytecode_point_n_vars = log_inner_bytecode + log2_ceil_usize(N_INSTRUCTION_COLUMNS);
    replacements.insert(
        "BYTECODE_SUMCHECK_PROOF_SIZE_PLACEHOLDER".to_string(),
        bytecode_reduction_sumcheck_proof_size(bytecode_point_n_vars).to_string(),
    );

    let mut one_buses_domseps = vec![];
    let mut one_buses_data_cols = vec![];
    let mut one_buses_data_offsets = vec![];
    let mut one_buses_new_cols = vec![];
    let mut num_cols_air = vec![];
    let mut n_air_columns = vec![];
    let mut n_air_shift_columns = vec![];
    let mut n_air_constraints = vec![];
    let mut one_buses_all_cols = vec![];
    let mut one_bus_runs = vec![];
    let mut n_column_buses = vec![];
    let mut column_bus_pull = vec![];
    let mut column_bus_offsets = vec![];
    let mut column_bus_total = 0usize;
    for table in ALL_TABLES {
        let dirs = column_bus_directions(&table.bus_interactions());
        column_bus_offsets.push(column_bus_total.to_string());
        column_bus_total += dirs.len();
        n_column_buses.push(dirs.len().to_string());
        column_bus_pull.push(format!(
            "[{}]",
            dirs.iter().map(|d| if matches!(d, BusDirection::Pull) { "1" } else { "0" }).collect::<Vec<_>>().join(", ")
        ));
        let mut table_domseps = vec![];
        let mut table_data_cols = vec![];
        let mut table_data_offsets = vec![];
        let mut table_new_cols = vec![];
        // (domsep, batchable): a bus is batchable when it opens exactly its one data column (offset 0);
        // maximal runs of consecutive batchable buses with one domsep (the range pushes) are verified
        // in batch by the recursion program.
        let mut bus_specs: Vec<(usize, bool)> = vec![];
        let mut seen_cols: HashSet<ColIndex> = HashSet::new();
        for bus in table.bus_interactions() {
            if !matches!(bus.multiplicity, BusMultiplicity::One) {
                continue;
            }
            let BusData::Constant(domsep) = bus.domainsep else {
                panic!("Multiplicity::One bus domsep must be a constant");
            };
            let mut data_cols = vec![];
            let mut data_offsets = vec![];
            let mut new_cols = vec![];
            for entry in &bus.data {
                let (col, ofs) = match entry {
                    BusData::Column(c) => (*c, 0),
                    BusData::ColumnPlusConstant(c, o) => (*c, *o),
                    BusData::Constant(_) => panic!("Multiplicity::One bus data must be a column"),
                };
                data_cols.push(col);
                data_offsets.push(ofs);
                if seen_cols.insert(col) {
                    new_cols.push(col);
                }
            }
            bus_specs.push((domsep, data_cols.len() == 1 && data_offsets[0] == 0 && new_cols.len() == 1 && new_cols[0] == data_cols[0]));
            table_domseps.push(domsep.to_string());
            table_data_cols.push(format!(
                "[{}]",
                data_cols.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            ));
            table_data_offsets.push(format!(
                "[{}]",
                data_offsets.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            ));
            table_new_cols.push(format!(
                "[{}]",
                new_cols.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
            ));
        }
        one_buses_domseps.push(format!("[{}]", table_domseps.join(", ")));
        one_buses_data_cols.push(format!("[{}]", table_data_cols.join(", ")));
        one_buses_data_offsets.push(format!("[{}]", table_data_offsets.join(", ")));
        one_buses_new_cols.push(format!("[{}]", table_new_cols.join(", ")));
        {
            let mut runs: Vec<String> = vec![];
            let mut i = 0;
            while i < bus_specs.len() {
                let (ds, batchable) = bus_specs[i];
                let mut n = 1;
                if batchable {
                    while i + n < bus_specs.len() && bus_specs[i + n] == (ds, true) { n += 1; }
                }
                runs.push(format!("[{i}, {n}, {}]", batchable as u8));
                i += n;
            }
            one_bus_runs.push(format!("[{}]", runs.join(", ")));
        }

        let mut sorted_seen: Vec<ColIndex> = seen_cols.iter().copied().collect();
        sorted_seen.sort();
        one_buses_all_cols.push(format!(
            "[{}]",
            sorted_seen.iter().map(usize::to_string).collect::<Vec<_>>().join(", ")
        ));

        num_cols_air.push(table.n_columns().to_string());
        n_air_columns.push(table.n_columns().to_string());
        n_air_shift_columns.push(table.n_shift_columns().to_string());
        n_air_constraints.push(table.n_constraints().to_string());
    }
    let max_num_cols_air = ALL_TABLES.iter().map(|t| t.n_columns()).max().unwrap();
    replacements.insert("MAX_NUM_COLS_AIR_PLACEHOLDER".to_string(), max_num_cols_air.to_string());
    {
        let mut offsets = vec![]; let mut acc = 0usize;
        for t in ALL_TABLES { offsets.push(acc.to_string()); acc += t.n_columns(); }
        replacements.insert("COLS_AIR_OFFSETS_PLACEHOLDER".to_string(), format!("[{}]", offsets.join(", ")));
        replacements.insert("TOTAL_NUM_COLS_AIR_PLACEHOLDER".to_string(), acc.to_string());
    }
    replacements.insert(
        "ONE_BUSES_ALL_COLS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_all_cols.join(", ")),
    );
    replacements.insert("ONE_BUS_RUNS_PLACEHOLDER".to_string(), format!("[{}]", one_bus_runs.join(", ")));
    replacements.insert(
        "ONE_BUSES_DOMSEPS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_domseps.join(", ")),
    );
    replacements.insert("N_COLUMN_BUSES_PLACEHOLDER".to_string(), format!("[{}]", n_column_buses.join(", ")));
    replacements.insert("COLUMN_BUS_PULL_PLACEHOLDER".to_string(), format!("[{}]", column_bus_pull.join(", ")));
    replacements.insert("COLUMN_BUS_OFFSETS_PLACEHOLDER".to_string(), format!("[{}]", column_bus_offsets.join(", ")));
    replacements.insert("TOTAL_COLUMN_BUSES_PLACEHOLDER".to_string(), column_bus_total.to_string());
    replacements.insert(
        "ONE_BUSES_DATA_COLS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_data_cols.join(", ")),
    );
    replacements.insert(
        "ONE_BUSES_DATA_OFFSETS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_data_offsets.join(", ")),
    );
    replacements.insert(
        "ONE_BUSES_NEW_COLS_PLACEHOLDER".to_string(),
        format!("[{}]", one_buses_new_cols.join(", ")),
    );
    replacements.insert(
        "NUM_COLS_AIR_PLACEHOLDER".to_string(),
        format!("[{}]", num_cols_air.join(", ")),
    );
    replacements.insert(
        "EXECUTION_TABLE_INDEX_PLACEHOLDER".to_string(),
        Table::execution().index().to_string(),
    );
    replacements.insert(
        "TOTAL_NUM_AIR_CONSTRAINTS_PLACEHOLDER".to_string(),
        total_air_constraints().to_string(),
    );
    replacements.insert(
        "N_AIR_CONSTRAINTS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_constraints.join(", ")),
    );
    let mut air_alpha_offsets = Vec::with_capacity(n_air_constraints.len());
    let mut cumul: usize = 0;
    for s in &n_air_constraints {
        air_alpha_offsets.push(cumul.to_string());
        cumul += s.parse::<usize>().unwrap();
    }
    replacements.insert(
        "AIR_ALPHA_OFFSETS_PLACEHOLDER".to_string(),
        format!("[{}]", air_alpha_offsets.join(", ")),
    );
    replacements.insert(
        "MAX_AIR_FULL_DEGREE_PLACEHOLDER".to_string(),
        (ALL_TABLES.iter().map(|t| t.degree_air()).max().unwrap() + 1).to_string(),
    );
    replacements.insert(
        "N_AIR_COLUMNS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_columns.join(", ")),
    );
    replacements.insert(
        "N_AIR_SHIFT_COLUMNS_PLACEHOLDER".to_string(),
        format!("[{}]", n_air_shift_columns.join(", ")),
    );
    replacements.insert(
        "EVALUATE_AIR_FUNCTIONS_PLACEHOLDER".to_string(),
        all_air_evals_in_zk_dsl(),
    );
    replacements.insert("AIR_DISPATCH_ARMS_PLACEHOLDER".to_string(), air_dispatch_arms());
    replacements.insert(
        "N_INSTRUCTION_COLUMNS_PLACEHOLDER".to_string(),
        N_INSTRUCTION_COLUMNS.to_string(),
    );
    replacements.insert(
        "TOTAL_WHIR_STATEMENTS_PLACEHOLDER".to_string(),
        total_whir_statements().to_string(),
    );
    replacements.insert("STARTING_PC_PLACEHOLDER".to_string(), STARTING_PC.to_string());
    replacements.insert("ENDING_PC_PLACEHOLDER".to_string(), ending_pc.to_string());

    // XMSS-specific replacements
    replacements.insert("V_PLACEHOLDER".to_string(), V.to_string());
    replacements.insert("W_PLACEHOLDER".to_string(), W.to_string());
    replacements.insert("TARGET_SUM_PLACEHOLDER".to_string(), TARGET_SUM.to_string());
    replacements.insert("LOG_LIFETIME_PLACEHOLDER".to_string(), LOG_LIFETIME.to_string());
    replacements.insert("MESSAGE_LEN_PLACEHOLDER".to_string(), DIGEST_LEN.to_string()); // the hashed message is one digest
    replacements.insert("RANDOMNESS_LEN_PLACEHOLDER".to_string(), RANDOMNESS_LEN_FE.to_string());
    replacements.insert(
        "PUBLIC_PARAM_LEN_FE_PLACEHOLDER".to_string(),
        PUBLIC_PARAM_LEN_FE.to_string(),
    );
    replacements.insert(
        "MERKLE_LEVELS_PER_CHUNK_PLACEHOLDER".to_string(),
        MERKLE_LEVELS_PER_CHUNK_FOR_SLOT.to_string(),
    );
    replacements.insert("XMSS_DIGEST_LEN_PLACEHOLDER".to_string(), XMSS_DIGEST_LEN.to_string());

    replacements.insert(
        "SINGLE_MESSAGE_FLAG_PLACEHOLDER".to_string(),
        SINGLE_MESSAGE_FLAG.to_string(),
    );
    replacements.insert(
        "MULTI_MESSAGE_FLAG_PLACEHOLDER".to_string(),
        MULTI_MESSAGE_FLAG.to_string(),
    );
    replacements.insert(
        "MAX_XMSS_AGGREGATED_PLACEHOLDER".to_string(),
        MAX_XMSS_AGGREGATED.to_string(),
    );
    replacements.insert(
        "MAX_XMSS_DUPLICATES_PLACEHOLDER".to_string(),
        MAX_XMSS_DUPLICATES.to_string(),
    );
    replacements.insert("MAX_RECURSIONS_PLACEHOLDER".to_string(), MAX_RECURSIONS.to_string());
    replacements.insert("ED25519_LEAF_FLAG_PLACEHOLDER".to_string(), ED25519_LEAF_FLAG.to_string());
    replacements.insert("ED25519_NODE_FLAG_PLACEHOLDER".to_string(), ED25519_NODE_FLAG.to_string());
    replacements.insert(
        "ED25519_SCHEME_ID_PLACEHOLDER".to_string(),
        lean_prover::ed25519_leaf::ED25519_SCHEME_ID.to_string(),
    );
    replacements.insert("ED25519_LEAF_VERSION_PLACEHOLDER".to_string(), lean_prover::ed25519_leaf::LEAF_VERSION.to_string());
    for (k, v) in lean_prover::ed25519_leaf::leaf_program_replacements() { replacements.insert(k, v); }

    // Bytecode zero eval
    replacements.insert(
        "BYTECODE_ZERO_EVAL_PLACEHOLDER".to_string(),
        bytecode_zero_eval.as_canonical_u64().to_string(),
    );
    replacements.insert("ZERO_VEC_LEN_PLACEHOLDER".to_string(), ZERO_VEC_LEN.to_string());
    replacements.insert(
        "NUM_REPEATED_ONES_PLACEHOLDER".to_string(),
        NUM_REPEATED_ONES.to_string(),
    );

    replacements
}

fn all_air_evals_in_zk_dsl() -> String {
    let mut res = String::new();
    res += &air_eval_in_zk_dsl(ExecutionTable::<false> {});
    res += &air_eval_in_zk_dsl(ExtensionOpPrecompile::<false> {});
    res += &air_eval_in_zk_dsl(Poseidon16Precompile::<false> {});
    res += &air_eval_in_zk_dsl(lean_vm::ed25519::EdSigTable::<false> {});
    res += &air_eval_in_zk_dsl(lean_vm::ed25519::EdDecompressTable::<false> {});
    res += &air_eval_in_zk_dsl(lean_vm::ed25519::Sha512Table::<false> {});
    res += &air_eval_in_zk_dsl(lean_vm::ed25519::ScalarLTable::<false> {});
    res += &air_eval_in_zk_dsl(lean_vm::ed25519::SignerScalarTable::<false> {});
    res += &air_eval_in_zk_dsl(lean_vm::ed25519::EdAddTable::<false> {});
    res
}

const AIR_INNER_VALUES_VAR: &str = "inner_evals";

struct AirCodegenCtx {
    expr_cache: HashMap<SymbolicNodeRef<F>, String>,
    consts_cache: HashMap<Vec<u32>, String>,
    ef_const_cache: HashMap<u32, String>,
    ctr: Counter,
}

impl AirCodegenCtx {
    fn new() -> Self {
        Self {
            expr_cache: HashMap::new(),
            consts_cache: HashMap::new(),
            ef_const_cache: HashMap::new(),
            ctr: Counter::new(),
        }
    }

    fn write_base_constants(&mut self, values: &[u32], res: &mut String) -> String {
        if let Some(name) = self.consts_cache.get(values) {
            return name.clone();
        }
        let name = format!("bc_{}", self.ctr.get_next());
        res.push_str(&format!("\n    {} = Array({})", name, values.len()));
        for (i, &c) in values.iter().enumerate() {
            res.push_str(&format!("\n    {}[{}] = {}", name, i, c));
        }
        self.consts_cache.insert(values.to_vec(), name.clone());
        name
    }

    fn write_embedded_constant(&mut self, c: u32, res: &mut String) -> String {
        if let Some(name) = self.ef_const_cache.get(&c) {
            return name.clone();
        }
        let name = format!("aux_{}", self.ctr.get_next());
        res.push_str(&format!("\n    {} = embed_in_ef({})", name, c));
        self.ef_const_cache.insert(c, name.clone());
        name
    }
}

fn air_eval_in_zk_dsl<T: TableT>(table: T) -> String
where
    T::ExtraData: Default,
{
    let (constraints, buses, identities) = get_symbolic_constraints_and_bus_data_values::<F, _>(&table);
    let mut ctx = AirCodegenCtx::new();

    let mut res = format!(
        "def evaluate_air_constraints_table_{}({}, air_alpha_powers, logup_beta_eq_poly):\n",
        table.table().index(),
        AIR_INNER_VALUES_VAR
    );

    let n_constraints = constraints.len();
    res += &format!("\n    constraints_buf = Array(DIM * {})", n_constraints);
    let identity_at: HashMap<usize, usize> = identities.iter().enumerate().map(|(k, id)| (id.first_constraint, k)).collect();
    let mut index = 0;
    while index < n_constraints {
        if let Some(&k) = identity_at.get(&index) {
            // a recorded G8 identity: 65 constraints through the loop-based helpers (g8.py)
            emit_g8_identity(&identities[k], &format!("constraints_buf + {} * DIM", index), &mut ctx, &mut res);
            index += G8_N_CONSTRAINTS;
            continue;
        }
        let dest = format!("constraints_buf + {} * DIM", index);
        eval_air_constraint(constraints[index], Some(&dest), &mut ctx, &mut res);
        index += 1;
    }

    // Column buses, in order: the j-th bus's multiplicity → alpha slot 2j, its fingerprint → slot 2j+1;
    // the AIR constraints follow at slot 2·n_buses. (`air_alpha_powers` is this table's alpha slice.)
    let alpha_at = |slot: usize| if slot == 0 { "air_alpha_powers".to_string() } else { format!("air_alpha_powers + {} * DIM", slot) };
    let n_buses = buses.len();
    for (j, (bus_multiplicity, bus_data)) in buses.iter().enumerate() {
        // `bus_data`'s last entry is the domainsep (logup domain separation).
        let (bus_domainsep, bus_real_data) = bus_data.split_last().unwrap();
        let multiplicity = eval_air_constraint(*bus_multiplicity, None, &mut ctx, &mut res);
        res += &format!("\n    buff_{j} = Array(DIM * {})", bus_real_data.len());
        for (i, data) in bus_real_data.iter().enumerate() {
            let data_str = eval_air_constraint(*data, None, &mut ctx, &mut res);
            res += &format!("\n    copy_ef({}, buff_{j} + DIM * {})", data_str, i);
        }
        let domainsep_str = eval_air_constraint(*bus_domainsep, None, &mut ctx, &mut res);
        // bus_res = sum(buff[i] * logup_beta_eq_poly[i]) + disc * logup_beta_eq_poly.last()
        res += &format!("\n    bus_res_init_{j} = Array(DIM)");
        res += &format!(
            "\n    dot_product_ee(buff_{j}, logup_beta_eq_poly, bus_res_init_{j}, {})",
            bus_real_data.len()
        );
        res += &format!(
            "\n    bus_res_{j} = add_extension_ret(mul_extension_ret({}, logup_beta_eq_poly + {} * DIM), bus_res_init_{j})",
            domainsep_str,
            (1 << LOG_MAX_BUS_WIDTH) - 1
        );
        res += &format!("\n    weighted_bus_{j} = mul_extension_ret(bus_res_{j}, {})", alpha_at(2 * j + 1));
        res += &format!("\n    weighted_multiplicity_{j} = mul_extension_ret({}, {})", alpha_at(2 * j), multiplicity);
        if j == 0 {
            res += &format!("\n    sum: Mut = add_extension_ret(weighted_bus_{j}, weighted_multiplicity_{j})");
        } else {
            res += &format!("\n    sum = add_extension_ret(sum, add_extension_ret(weighted_bus_{j}, weighted_multiplicity_{j}))");
        }
    }

    res += "\n    weighted_constraints = Array(DIM)";
    res += &format!(
        "\n    dot_product_ee({}, constraints_buf, weighted_constraints, {})",
        alpha_at(2 * n_buses),
        n_constraints
    );
    if n_buses == 0 {
        res += "\n    sum: Mut = weighted_constraints";
    } else {
        res += "\n    sum = add_extension_ret(sum, weighted_constraints)";
    }

    res += "\n    return sum";
    res += "\n";
    res
}

/// A limb vector as a zkDSL pointer: consecutive column openings are passed as `inner_evals + DIM*k`,
/// anything else is materialized into a fresh buffer.
/// One match arm per table, so every dispatcher (production and test) covers 0..N_TABLES from the
/// same source (the stock program had 3 hand-written arms, which broke silently at 9 tables).
fn air_dispatch_arms() -> String {
    (0..N_TABLES)
        .map(|i| format!("case {i}:\n            res = evaluate_air_constraints_table_{i}(inner_evals, air_alpha_powers, logup_beta_eq_poly)"))
        .collect::<Vec<_>>()
        .join("\n        ")
}

fn g8_operand(exprs: &[SymbolicExpression<F>], ctx: &mut AirCodegenCtx, res: &mut String) -> String {
    let consecutive = exprs.iter().enumerate().all(|(i, e)| matches!(e, SymbolicExpression::Variable(v) if v.index == match exprs[0] { SymbolicExpression::Variable(v0) => v0.index + i, _ => usize::MAX }));
    if consecutive && !exprs.is_empty() {
        if let SymbolicExpression::Variable(v0) = exprs[0] {
            return format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, v0.index);
        }
    }
    let name = format!("g8v_{}", ctx.ctr.get_next());
    res.push_str(&format!("\n    {} = Array(DIM * {})", name, exprs.len()));
    for (i, e) in exprs.iter().enumerate() {
        let dest = format!("{} + DIM * {}", name, i);
        eval_air_constraint(*e, Some(&dest), ctx, res);
    }
    name
}

fn emit_g8_identity(id: &SymbolicG8Identity<F>, dest: &str, ctx: &mut AirCodegenCtx, res: &mut String) {
    let gate = eval_air_constraint(id.gate, None, ctx, res);
    let mut v = format!("g8v_{}", ctx.ctr.get_next());
    res.push_str(&format!("\n    {} = g8_zero()", v));
    for (a, b, pos) in &id.products {
        let a_ptr = g8_operand(a, ctx, res);
        let b_ptr = g8_operand(b, ctx, res);
        let b_rev = format!("g8v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = g8_rev({})", b_rev, b_ptr));
        let nv = format!("g8v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = {}({}, {}, {})", nv, if *pos { "g8_conv_add" } else { "g8_conv_sub" }, v, a_ptr, b_rev));
        v = nv;
    }
    for (c, pos) in &id.linears {
        let c_ptr = g8_operand(c, ctx, res);
        let nv = format!("g8v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = {}({}, {})", nv, if *pos { "g8_lin_add" } else { "g8_lin_sub" }, v, c_ptr));
        v = nv;
    }
    if let Some(r) = &id.r {
        let r_ptr = g8_operand(r, ctx, res);
        let nv = format!("g8v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = g8_lin_sub({}, {})", nv, v, r_ptr));
        v = nv;
    }
    let q_ptr = g8_operand(&id.q, ctx, res);
    let m_rev: Vec<u32> = id.modulus.iter().rev().map(|b| *b as u32).collect();
    let m_name = ctx.write_base_constants(&m_rev, res);
    let nv = format!("g8v_{}", ctx.ctr.get_next());
    res.push_str(&format!("\n    {} = g8_qsub({}, {}, {})", nv, v, q_ptr, m_name));
    v = nv;
    let w_ptr = g8_operand(&id.w, ctx, res);
    res.push_str(&format!("\n    g8_chain({}, {}, {}, {})", dest, gate, v, w_ptr));
}

fn eval_air_constraint(
    expr: SymbolicExpression<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> String {
    let v = match expr {
        SymbolicExpression::Constant(c) => ctx.write_embedded_constant(c.as_canonical_u32(), res),
        SymbolicExpression::Variable(v) => format!("{} + DIM * {}", AIR_INNER_VALUES_VAR, v.index),
        SymbolicExpression::Operation(idx) => {
            if let Some(v) = ctx.expr_cache.get(&idx) {
                v.clone()
            } else if let Some(v) = try_emit_dot_product_be(idx, dest, ctx, res) {
                ctx.expr_cache.insert(idx, v.clone());
                return v;
            } else {
                let node = *idx;
                let v = match node.op {
                    SymbolicOperation::Neg => {
                        let a = eval_air_constraint(node.lhs, None, ctx, res);
                        let v = format!("aux_{}", ctx.ctr.get_next());
                        res.push_str(&format!("\n    {} = opposite_extension_ret({})", v, a));
                        v
                    }
                    _ => eval_air_binary_op(node.op, node.lhs, node.rhs, dest, ctx, res),
                };
                ctx.expr_cache.insert(idx, v.clone());
                v
            }
        }
    };
    if let Some(d) = dest
        && v != d
    {
        res.push_str(&format!("\n    copy_ef({}, {})", v, d));
    }
    v
}

/// Detect `0 + c0*x0 + c1*x1 + ... + cn*xn` in the expression tree and emit
/// a single `dot_product_be` precompile call. Returns None if the pattern doesn't match.
fn try_emit_dot_product_be(
    idx: SymbolicNodeRef<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> Option<String> {
    // Walk the left-spine of Add(_, Mul(Const, _)) nodes down to Constant(ZERO).
    let mut constants = Vec::new();
    let mut operands = Vec::new();
    let mut current = SymbolicExpression::<F>::Operation(idx);
    loop {
        match current {
            SymbolicExpression::Constant(c) if c == F::ZERO && constants.len() >= 2 => break,
            SymbolicExpression::Operation(op_idx) => {
                if op_idx != idx && ctx.expr_cache.contains_key(&op_idx) {
                    return None;
                }
                let node = *op_idx;
                if node.op != SymbolicOperation::Add {
                    return None;
                }
                let mul_idx = match node.rhs {
                    SymbolicExpression::Operation(i) => i,
                    _ => return None,
                };
                let mul = *mul_idx;
                if mul.op != SymbolicOperation::Mul {
                    return None;
                }
                let (c, expr) = match (mul.lhs, mul.rhs) {
                    (SymbolicExpression::Constant(c), o) | (o, SymbolicExpression::Constant(c)) => {
                        (c.as_canonical_u32(), o)
                    }
                    _ => return None,
                };
                constants.push(c);
                operands.push(expr);
                current = node.lhs;
            }
            _ => return None,
        }
    }
    constants.reverse();
    operands.reverse();
    let n = constants.len();

    let consts = ctx.write_base_constants(&constants, res);

    // Reuse an existing contiguous buffer if possible.
    let vals = try_find_contiguous_buffer(&operands, ctx).unwrap_or_else(|| {
        let buf = format!("dp_v_{}", ctx.ctr.get_next());
        res.push_str(&format!("\n    {} = Array(DIM * {})", buf, n));
        for (i, ext) in operands.iter().enumerate() {
            eval_air_constraint(*ext, Some(&format!("{} + DIM * {}", buf, i)), ctx, res);
        }
        buf
    });

    let dp_dest = dest.map_or_else(
        || {
            let v = format!("aux_{}", ctx.ctr.get_next());
            res.push_str(&format!("\n    {} = Array(DIM)", v));
            v
        },
        |d| d.to_string(),
    );
    res.push_str(&format!(
        "\n    dot_product_be({}, {}, {}, {})",
        consts, vals, dp_dest, n
    ));
    Some(dp_dest)
}

/// Check whether every operand is already cached as consecutive slots in the
/// same buffer (`buf + DIM * 0`, `buf + DIM * 1`, …).
fn try_find_contiguous_buffer(operands: &[SymbolicExpression<F>], ctx: &AirCodegenCtx) -> Option<String> {
    let mut base: Option<&str> = None;
    for (i, op) in operands.iter().enumerate() {
        let idx = match op {
            SymbolicExpression::Operation(idx) => *idx,
            _ => return None,
        };
        let suffix = format!(" + DIM * {}", i);
        let this_base = ctx.expr_cache.get(&idx)?.strip_suffix(&suffix)?;
        match base {
            None => base = Some(this_base),
            Some(b) if b == this_base => {}
            _ => return None,
        }
    }
    base.map(|s| s.to_string())
}

fn eval_air_binary_op(
    op: SymbolicOperation,
    lhs: SymbolicExpression<F>,
    rhs: SymbolicExpression<F>,
    dest: Option<&str>,
    ctx: &mut AirCodegenCtx,
    res: &mut String,
) -> String {
    let c0 = match lhs {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };
    let c1 = match rhs {
        SymbolicExpression::Constant(c) => Some(c.as_canonical_u32()),
        _ => None,
    };

    match (c0, c1) {
        // Both extension
        (None, None) => {
            let a = eval_air_constraint(lhs, None, ctx, res);
            let b = eval_air_constraint(rhs, None, ctx, res);
            if let Some(d) = dest {
                let f = match op {
                    SymbolicOperation::Mul => "mul_extension",
                    SymbolicOperation::Add => "add_ee",
                    SymbolicOperation::Sub => "sub_extension",
                    _ => unreachable!(),
                };
                res.push_str(&format!("\n    {}({}, {}, {})", f, a, b, d));
                d.to_string()
            } else {
                let f = match op {
                    SymbolicOperation::Mul => "mul_extension_ret",
                    SymbolicOperation::Add => "add_extension_ret",
                    SymbolicOperation::Sub => "sub_extension_ret",
                    _ => unreachable!(),
                };
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, a, b));
                v
            }
        }
        // Mul/Add with a base-field constant
        _ if matches!(op, SymbolicOperation::Mul | SymbolicOperation::Add) => {
            let (c, ext_expr) = match (c0, c1) {
                (Some(c), _) => (c, rhs),
                (_, Some(c)) => (c, lhs),
                _ => unreachable!(),
            };
            let ext = eval_air_constraint(ext_expr, None, ctx, res);
            if let Some(d) = dest {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "dot_product_be"
                } else {
                    "add_be"
                };
                let scalar = ctx.write_base_constants(&[c], res);
                res.push_str(&format!("\n    {}({}, {}, {})", f, scalar, ext, d));
                d.to_string()
            } else {
                let f = if matches!(op, SymbolicOperation::Mul) {
                    "mul_base_extension_ret"
                } else {
                    "add_base_extension_ret"
                };
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = {}({}, {})", v, f, c, ext));
                v
            }
        }
        // Sub: base - ext
        (Some(c), _) => {
            let ext = eval_air_constraint(rhs, None, ctx, res);
            let v = format!("aux_{}", ctx.ctr.get_next());
            res.push_str(&format!("\n    {} = sub_base_extension_ret({}, {})", v, c, ext));
            v
        }
        // Sub: ext - base
        (_, Some(c)) => {
            let ext = eval_air_constraint(lhs, None, ctx, res);
            if let Some(d) = dest {
                let scalar = ctx.write_base_constants(&[c], res);
                res.push_str(&format!("\n    add_be({}, {}, {})", scalar, d, ext));
                d.to_string()
            } else {
                let v = format!("aux_{}", ctx.ctr.get_next());
                res.push_str(&format!("\n    {} = sub_extension_base_ret({}, {})", v, ext, c));
                v
            }
        }
    }
}

/// Every generated zkDSL evaluator equals the native `eval_extension` of its table on random inputs
/// (runner-level, no proof) — the check that the loop-based G8 emission is exact.
#[test]
fn test_zk_dsl_air_evaluators_match_native() {
    use lean_vm::ExtraDataForBuses;
    let mut x = 0x2545f4914f6cdd1du64;
    let mut nb = move || { x ^= x << 13; x ^= x >> 7; x ^= x << 17; x };
    let mut rand_ef = |nb: &mut dyn FnMut() -> u64| -> EF { EF::from_basis_coefficients_fn(|_| F::from_usize((nb() % F::ORDER_U64) as usize)) };
    let cells = |v: &[EF]| -> Vec<F> { v.iter().flat_map(|e| e.as_basis_coefficients_slice().to_vec()).collect() };
    for table in ALL_TABLES {
        let n_evals = table.n_columns() + table.n_shift_columns();
        let n_alphas = table.n_constraints();
        let n_betas = 1 << LOG_MAX_BUS_WIDTH;
        let evals: Vec<EF> = (0..n_evals).map(|_| rand_ef(&mut nb)).collect();
        let alphas: Vec<EF> = (0..n_alphas).map(|_| rand_ef(&mut nb)).collect();
        let betas: Vec<EF> = (0..n_betas).map(|_| rand_ef(&mut nb)).collect();
        let extra = ExtraDataForBuses::new(&betas, alphas.clone());
        macro_rules! native { ($t:expr) => {{ <_ as SumcheckComputation<EF>>::eval_extension($t, &evals, &extra) }}; }
        let expected: EF = delegate_to_inner!(&table => native);
        let mut replacements = build_replacements(18, F::ZERO);
        replacements.insert("N_EVALS_PLACEHOLDER".to_string(), n_evals.to_string());
        replacements.insert("N_ALPHAS_PLACEHOLDER".to_string(), n_alphas.to_string());
        replacements.insert("N_BETAS_PLACEHOLDER".to_string(), n_betas.to_string());
        replacements.insert("N_TABLES_PLACEHOLDER".to_string(), N_TABLES.to_string());
        replacements.insert("AIR_DISPATCH_ARMS_PLACEHOLDER".to_string(), air_dispatch_arms());
        let bytecode = compile_program_with_flags(&ProgramSource::Embedded { entry: "air_eval_test.py".to_string(), dir: &EMBEDDED_ZK_DSL }, CompilationFlags { replacements });
        let mut hints = Hints::default();
        hints.insert(&bytecode, "evals", arena_vec![ArenaVec::from_slice(&cells(&evals))]);
        hints.insert(&bytecode, "alphas", arena_vec![ArenaVec::from_slice(&cells(&alphas))]);
        hints.insert(&bytecode, "betas", arena_vec![ArenaVec::from_slice(&cells(&betas))]);
        hints.insert(&bytecode, "expect", arena_vec![ArenaVec::from_slice(&cells(&[expected]))]);
        hints.insert(&bytecode, "table_index", arena_vec![arena_vec![F::from_usize(table.index())]]);
        let witness = ExecutionWitness { hints, preamble_memory_len: PREAMBLE_MEMORY_LEN, ..Default::default() };
        let res = try_execute_bytecode(&bytecode, &[F::ZERO; PUBLIC_INPUT_LEN], &witness, false);
        match &res {
            Ok(r) => println!("{}: zkDSL evaluator == native ({} cycles, bytecode 2^{})", table.name(), r.pcs.len(), bytecode.log_size()),
            Err(e) => println!("{}: MISMATCH / runner error: {e:?}", table.name()),
        }
        assert!(res.is_ok(), "{}: the zkDSL evaluator disagrees with the native AIR", table.name());
    }
}

#[test]
fn display_all_air_evals_in_zk_dsl() {
    println!("{}", all_air_evals_in_zk_dsl());
}

#[test]
fn display_poseidon_air_in_zk_dsl() {
    println!("{}", air_eval_in_zk_dsl(Poseidon16Precompile::<false> {}));
}

/// The self-referential recursion program must compile (and converge) with the current tables' bus
/// layout — this is what validates the generated zkDSL verifier loops after any table/bus change.
#[test]
fn test_compile_recursion_program_converges() {
    let bytecode = compile_main_program_self_referential();
    assert!(bytecode.log_size() <= MAX_BYTECODE_LOG_SIZE);
    println!("recursion program: log_size {} ending_pc {}", bytecode.log_size(), bytecode.ending_pc());
}
