use crate::execution::memory::MemoryAccess;
use crate::{EF, F, InstructionContext, LOGUP_MEMORY_DOMAINSEP, PrecompileCompTimeArgs, RunnerError, Table};
use backend::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};

pub type ColIndex = usize;

/// Each entry: (point, eval, eval at 'shifted-down' column).
pub type CommittedStatements =
    BTreeMap<Table, Vec<(MultilinearPoint<EF>, BTreeMap<ColIndex, EF>, BTreeMap<ColIndex, EF>)>>;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BusDirection {
    Pull,
    Push,
}

impl BusDirection {
    pub fn to_field_flag(self) -> F {
        match self {
            BusDirection::Pull => F::NEG_ONE,
            BusDirection::Push => F::ONE,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BusData {
    Column(ColIndex),
    ColumnPlusConstant(ColIndex, usize),
    Constant(usize),
}

impl BusData {
    pub fn column(self) -> Option<ColIndex> {
        match self {
            Self::Column(c) | Self::ColumnPlusConstant(c, _) => Some(c),
            Self::Constant(_) => None,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub enum BusMultiplicity {
    One,
    Column(ColIndex),
}

#[derive(Debug)]
pub struct BusInteraction {
    pub direction: BusDirection,
    pub multiplicity: BusMultiplicity,
    pub domainsep: BusData,
    pub data: Vec<BusData>,
}

impl BusInteraction {
    pub fn is_memory_lookup(&self) -> bool {
        matches!(self.domainsep, BusData::Constant(LOGUP_MEMORY_DOMAINSEP))
    }
}

/// Directions of a table's Column-multiplicity buses, in `bus_interactions()` order.
///
/// CONVENTION (checked by `test_column_buses_first`): every Column-multiplicity bus precedes every
/// Multiplicity::One bus, and the table's AIR emits one `eval_bus_virtual` per Column bus, in this
/// order, before any other constraint — so the j-th Column bus owns alpha slots 2j and 2j+1.
pub fn column_bus_directions(buses: &[BusInteraction]) -> Vec<BusDirection> {
    buses
        .iter()
        .filter(|b| matches!(b.multiplicity, BusMultiplicity::Column(_)))
        .map(|b| b.direction)
        .collect()
}

pub fn n_column_buses(buses: &[BusInteraction]) -> usize {
    column_bus_directions(buses).len()
}

/// A structural LogUp range section: rows idx ∈ [0, 2^log_rows); a pushed value v (One-bus, data [v],
/// domainsep `domainsep`) balances only against row v with the ALIVE domainsep, which the section uses
/// for idx < 2^bits and replaces by `dead_domainsep` above — so v is proven < 2^bits (spec F1: never a
/// scaled or combined value; one column per push).
#[derive(Debug, Clone, Copy)]
pub struct RangeSection { pub domainsep: usize, pub dead_domainsep: usize, pub log_rows: usize, pub bits: usize }
pub const RANGE_U16: usize = 0;
pub const RANGE_U10: usize = 1;
pub const RANGE_U8: usize = 2;
pub const RANGE_U7: usize = 3;
pub const RANGE_U5: usize = 4;
pub const RANGE_U4: usize = 5;
pub const N_RANGE_SECTIONS: usize = 6;
/// Sections in descending size, summing to exactly 2^RANGE_LOG_TOTAL, so every section is aligned
/// within the region. Domainseps in the free class 2 mod 4 (memory 1, bytecode 2, Poseidon odd ≥ 3,
/// ExtensionOp 0 mod 4, precompiles 6/10/14/...).
pub const RANGE_SECTIONS: [RangeSection; N_RANGE_SECTIONS] = [
    RangeSection { domainsep: 34, dead_domainsep: 38, log_rows: 16, bits: 16 },
    RangeSection { domainsep: 42, dead_domainsep: 46, log_rows: 16, bits: 10 },
    RangeSection { domainsep: 50, dead_domainsep: 54, log_rows: 16, bits: 8 },
    RangeSection { domainsep: 58, dead_domainsep: 62, log_rows: 15, bits: 7 },
    RangeSection { domainsep: 66, dead_domainsep: 70, log_rows: 14, bits: 5 },
    RangeSection { domainsep: 74, dead_domainsep: 78, log_rows: 14, bits: 4 },
];
pub const RANGE_LOG_TOTAL: usize = 18;
pub const RANGE_MIN_LOG_ALIGN: usize = RANGE_LOG_TOTAL; // the bytecode block is padded to ≥ the region, so the region start is aligned to it
pub const fn range_total_rows() -> usize { let mut t = 0; let mut i = 0; while i < N_RANGE_SECTIONS { t += 1 << RANGE_SECTIONS[i].log_rows; i += 1; } t }
const _: () = assert!(range_total_rows() == 1 << RANGE_LOG_TOTAL);
/// LogUp/stacked layout: memory | bytecode block | range region | tables (sorted by height desc).
/// The bytecode block is padded to max(bytecode, largest table, 2^16) so the region starts aligned;
/// the region is padded to max(2^18, largest table) so the tables after it stay aligned.
pub const fn bytecode_block_log(log_bytecode: usize, max_table_log: usize) -> usize {
    let a = if log_bytecode > max_table_log { log_bytecode } else { max_table_log };
    if a > RANGE_MIN_LOG_ALIGN { a } else { RANGE_MIN_LOG_ALIGN }
}
pub const fn range_region_log(max_table_log: usize) -> usize { if max_table_log > RANGE_LOG_TOTAL { max_table_log } else { RANGE_LOG_TOTAL } }
pub fn range_section_of(domainsep: usize) -> Option<usize> { RANGE_SECTIONS.iter().position(|s| s.domainsep == domainsep) }
impl BusInteraction {
    pub fn range_section(&self) -> Option<usize> { match self.domainsep { BusData::Constant(ds) => range_section_of(ds), _ => None } }
}
/// One range push per column into `section`.
pub fn range_lookups(cols: &[ColIndex], section: usize) -> Vec<BusInteraction> {
    cols.iter().map(|&c| BusInteraction { direction: BusDirection::Push, multiplicity: BusMultiplicity::One, domainsep: BusData::Constant(RANGE_SECTIONS[section].domainsep), data: vec![BusData::Column(c)] }).collect()
}

pub fn memory_lookups_consecutive(idx_col: ColIndex, values_start: ColIndex, n: usize) -> Vec<BusInteraction> {
    (0..n)
        .map(|i| BusInteraction {
            direction: BusDirection::Push,
            multiplicity: BusMultiplicity::One,
            domainsep: BusData::Constant(LOGUP_MEMORY_DOMAINSEP),
            data: vec![
                BusData::ColumnPlusConstant(idx_col, i),
                BusData::Column(values_start + i),
            ],
        })
        .collect()
}

pub fn memory_lookup_groups(buses: &[BusInteraction]) -> Vec<MemoryLookupGroup> {
    let mut groups: Vec<MemoryLookupGroup> = Vec::new();
    let mut i = 0;
    while i < buses.len() {
        if !buses[i].is_memory_lookup() {
            i += 1;
            continue;
        }
        let (idx_col, first_ofs) = match buses[i].data[0] {
            BusData::ColumnPlusConstant(c, ofs) => (c, ofs),
            _ => unreachable!("memory-lookup bus shape is enforced by memory_lookups_consecutive"),
        };
        if first_ofs != 0 {
            let value_col = match buses[i].data[1] {
                BusData::Column(c) => c,
                _ => unreachable!("memory-lookup bus shape is enforced by memory_lookups_consecutive"),
            };
            groups.push(MemoryLookupGroup {
                start_bus: i,
                idx_col,
                value_cols: vec![value_col],
            });
            i += 1;
            continue;
        }
        let mut value_cols = Vec::new();
        let start = i;
        let mut expected_ofs = 0;
        while i < buses.len() && buses[i].is_memory_lookup() {
            let ok = matches!(
                buses[i].data[0],
                BusData::ColumnPlusConstant(c, ofs) if c == idx_col && ofs == expected_ofs
            );
            if !ok {
                break;
            }
            let value_col = match buses[i].data[1] {
                BusData::Column(c) => c,
                _ => unreachable!("memory-lookup bus shape is enforced by memory_lookups_consecutive"),
            };
            value_cols.push(value_col);
            i += 1;
            expected_ofs += 1;
        }
        groups.push(MemoryLookupGroup {
            start_bus: start,
            idx_col,
            value_cols,
        });
    }
    groups
}

#[derive(Debug)]
pub struct MemoryLookupGroup {
    pub start_bus: usize,
    pub idx_col: ColIndex,
    pub value_cols: Vec<ColIndex>,
}

#[derive(Debug, Default)]
pub struct TableTrace {
    pub columns: Vec<ArenaVec<F>>,
    pub non_padded_n_rows: usize,
    pub log_n_rows: VarCount,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            columns: (0..air.n_columns_total()).map(|_| ArenaVec::new()).collect(),
            non_padded_n_rows: 0, // filled later
            log_n_rows: 0,        // filled later
        }
    }
}

pub fn sort_tables_by_height(tables_log_heights: &BTreeMap<Table, usize>) -> Vec<(Table, usize)> {
    let mut tables_heights_sorted = tables_log_heights.clone().into_iter().collect::<Vec<_>>();
    tables_heights_sorted.sort_by_key(|&(_, h)| Reverse(h));
    tables_heights_sorted
}

#[derive(Debug, Default)]
pub struct ExtraDataForBuses<EF: KoalaBearExtension> {
    // GKR quotient challenges
    pub logup_alphas_eq_poly: Vec<EF>,
    pub logup_alphas_eq_poly_packed: Vec<EFPacking<EF>>,
    pub alpha_powers: Vec<EF>,
}
impl<EF: KoalaBearExtension> ExtraDataForBuses<EF> {
    pub fn new(logup_alphas_eq_poly: &[EF], alpha_powers: Vec<EF>) -> Self {
        let logup_alphas_eq_poly_packed = logup_alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
        Self {
            logup_alphas_eq_poly: logup_alphas_eq_poly.to_vec(),
            logup_alphas_eq_poly_packed,
            alpha_powers,
        }
    }
}

impl AlphaPowersMut<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        &mut self.alpha_powers
    }
}

impl AlphaPowers<EF> for ExtraDataForBuses<EF> {
    fn alpha_powers(&self) -> &[EF] {
        &self.alpha_powers
    }
}

impl<EF: KoalaBearExtension> ExtraDataForBuses<EF> {
    pub fn transmute_bus_data<NewEF: 'static>(&self) -> &Vec<NewEF> {
        if TypeId::of::<NewEF>() == TypeId::of::<EF>() {
            unsafe { transmute::<&Vec<EF>, &Vec<NewEF>>(&self.logup_alphas_eq_poly) }
        } else {
            assert_eq!(TypeId::of::<NewEF>(), TypeId::of::<EFPacking<EF>>());
            unsafe { transmute::<&Vec<EFPacking<EF>>, &Vec<NewEF>>(&self.logup_alphas_eq_poly_packed) }
        }
    }
}

/// Convention: The "AIR" columns are at the start (both for base and extension columns).
/// (Some columns may not appear in the AIR)
pub trait TableT: Air {
    fn name(&self) -> &'static str;
    fn table(&self) -> Table;
    fn bus_interactions(&self) -> Vec<BusInteraction>;
    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize, ending_pc: usize) -> Vec<F>;
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError>;

    // number of columns committed + potentially some virtual columns (useful to keep in memory for logup)
    fn n_columns_total(&self) -> usize {
        self.n_columns()
    }

    fn is_execution_table(&self) -> bool {
        false
    }
}
