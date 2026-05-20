use crate::execution::memory::MemoryAccess;
use crate::{EF, F, InstructionContext, LOGUP_MEMORY_DOMAINSEP, PrecompileCompTimeArgs, RunnerError, Table};
use backend::*;

use std::{any::TypeId, cmp::Reverse, collections::BTreeMap, mem::transmute};
use utils::VarCount;

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
pub enum Multiplicity {
    One,
    Column(ColIndex),
}

#[derive(Debug)]
pub struct Bus {
    pub direction: BusDirection,
    pub multiplicity: Multiplicity,
    pub domainsep: BusData,
    pub data: Vec<BusData>,
}

impl Bus {
    pub fn is_memory_lookup(&self) -> bool {
        matches!(self.domainsep, BusData::Constant(LOGUP_MEMORY_DOMAINSEP))
    }

    /// For memory-lookup buses, returns `(idx_col, offset, val_col)`.
    pub fn as_memory_lookup(&self) -> (ColIndex, usize, ColIndex) {
        match self.data.as_slice() {
            [BusData::ColumnPlusConstant(i, o), BusData::Column(v)] => (*i, *o, *v),
            _ => panic!("memory-lookup bus must have data = [CPC(index, offset), Column(value)]"),
        }
    }
}

pub fn memory_lookups_consecutive(idx_col: ColIndex, values_start: ColIndex, n: usize) -> impl Iterator<Item = Bus> {
    (0..n).map(move |i| Bus {
        direction: BusDirection::Push,
        multiplicity: Multiplicity::One,
        domainsep: BusData::Constant(LOGUP_MEMORY_DOMAINSEP),
        data: vec![
            BusData::ColumnPlusConstant(idx_col, i),
            BusData::Column(values_start + i),
        ],
    })
}

/// Group consecutive memory-lookup buses into `(idx_col, [val_col_0, val_col_1, …])`,
/// matching the original `LookupIntoMemory` layout.
pub fn memory_lookup_groups<T: TableT + ?Sized>(table: &T) -> Vec<(ColIndex, Vec<ColIndex>)> {
    let mut groups: Vec<(ColIndex, Vec<ColIndex>)> = Vec::new();
    for bus in table.buses().iter().filter(|b| b.is_memory_lookup()) {
        let (idx_col, offset, val_col) = bus.as_memory_lookup();
        if offset == 0 {
            groups.push((idx_col, vec![val_col]));
        } else {
            let last = groups.last_mut().expect("non-zero offset must follow offset=0");
            assert_eq!(last.0, idx_col, "memory bus run must share index column");
            assert_eq!(last.1.len(), offset, "memory bus offsets must be consecutive 0,1,2,…");
            last.1.push(val_col);
        }
    }
    groups
}

#[derive(Debug, Default)]
pub struct TableTrace {
    pub columns: Vec<Vec<F>>,
    pub non_padded_n_rows: usize,
    pub log_n_rows: VarCount,
}

impl TableTrace {
    pub fn new<A: TableT>(air: &A) -> Self {
        Self {
            columns: vec![Vec::new(); air.n_columns_total()],
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
pub struct ExtraDataForBuses<EF: ExtensionField<PF<EF>>> {
    // GKR quotient challenges (no separate `bus_beta` anymore — the AIR alpha at
    // `alpha^1` plays that role as the random combiner between the bus's two
    // constraints: `multiplicity` (alpha^0) and `fingerprint` (alpha^1)).
    pub logup_alphas_eq_poly: Vec<EF>,
    pub logup_alphas_eq_poly_packed: Vec<EFPacking<EF>>,
    pub alpha_powers: Vec<EF>,
}
impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
    pub fn new(logup_alphas_eq_poly: Vec<EF>, alpha_powers: Vec<EF>) -> Self {
        let logup_alphas_eq_poly_packed = logup_alphas_eq_poly.iter().map(|a| EFPacking::<EF>::from(*a)).collect();
        Self {
            logup_alphas_eq_poly,
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

impl<EF: ExtensionField<PF<EF>>> ExtraDataForBuses<EF> {
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
    fn buses(&self) -> Vec<Bus>;
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

    /// Total number of `assert_zero` / `assert_zero_ef` calls the AIR makes
    /// (excluding the primary bus, which uses `alpha^0`):
    /// `Air::logup_claim_columns().len()` extra degree-1 constraints + `n_constraints()`
    /// AIR constraints.
    fn n_total_constraints(&self) -> usize {
        // `Air::logup_claim_columns` is inherited via `TableT: Air`.
        <Self as backend::Air>::logup_claim_columns(self).len() + self.n_constraints()
    }
}
