use backend::*;

use crate::execution::memory::MemoryAccess;
use crate::*;
use crate::tables::ed25519::{EdAddTable, EdDecompressTable, EdSigTable, ScalarLTable, Sha512Table, SignerScalarTable};

pub const N_TABLES: usize = 9;
pub const ALL_TABLES: [Table; N_TABLES] = [Table::execution(), Table::extension_op(), Table::poseidon16(), Table::ed_sig(), Table::ed_decompress(), Table::sha512(), Table::scalar_l(), Table::signer_scalar(), Table::ed_add()];
pub const MAX_BUS_WIDTH: usize = 16; // ≥ bytecode (N_INSTRUCTION_COLUMNS + 2) and the 15-entry chunk tuples of EdAdd
pub const LOG_MAX_BUS_WIDTH: usize = log2_ceil_usize(MAX_BUS_WIDTH);

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(usize)]
pub enum Table {
    Execution(ExecutionTable<true>),
    ExtensionOp(ExtensionOpPrecompile<true>),
    Poseidon16(Poseidon16Precompile<true>),
    EdSig(EdSigTable<true>),
    EdDecompress(EdDecompressTable<true>),
    Sha512(Sha512Table<true>),
    ScalarL(ScalarLTable<true>),
    SignerScalar(SignerScalarTable<true>),
    EdAdd(EdAddTable<true>),
}

#[macro_export]
macro_rules! delegate_to_inner {
    // Existing pattern for method calls
    ($self:expr, $method:ident $(, $($arg:expr),*)?) => {
        match $self {
            Self::ExtensionOp(p) => p.$method($($($arg),*)?),
            Self::Poseidon16(p) => p.$method($($($arg),*)?),
            Self::Execution(p) => p.$method($($($arg),*)?),
            Self::EdSig(p) => p.$method($($($arg),*)?),
            Self::EdDecompress(p) => p.$method($($($arg),*)?),
            Self::Sha512(p) => p.$method($($($arg),*)?),
            Self::ScalarL(p) => p.$method($($($arg),*)?),
            Self::SignerScalar(p) => p.$method($($($arg),*)?),
            Self::EdAdd(p) => p.$method($($($arg),*)?),
        }
    };
    // New pattern for applying a macro to the inner value
    ($self:expr => $macro_name:ident) => {
        match $self {
            Table::ExtensionOp(p) => $macro_name!(p),
            Table::Poseidon16(p) => $macro_name!(p),
            Table::Execution(p) => $macro_name!(p),
            Table::EdSig(p) => $macro_name!(p),
            Table::EdDecompress(p) => $macro_name!(p),
            Table::Sha512(p) => $macro_name!(p),
            Table::ScalarL(p) => $macro_name!(p),
            Table::SignerScalar(p) => $macro_name!(p),
            Table::EdAdd(p) => $macro_name!(p),
        }
    };
}

impl Table {
    pub const fn execution() -> Self {
        Self::Execution(ExecutionTable)
    }
    pub const fn extension_op() -> Self {
        Self::ExtensionOp(ExtensionOpPrecompile)
    }
    pub const fn poseidon16() -> Self {
        Self::Poseidon16(Poseidon16Precompile)
    }
    pub const fn ed_sig() -> Self {
        Self::EdSig(EdSigTable)
    }
    pub const fn ed_decompress() -> Self {
        Self::EdDecompress(EdDecompressTable)
    }
    pub const fn sha512() -> Self {
        Self::Sha512(Sha512Table)
    }
    pub const fn scalar_l() -> Self {
        Self::ScalarL(ScalarLTable)
    }
    pub const fn signer_scalar() -> Self {
        Self::SignerScalar(SignerScalarTable)
    }
    pub const fn ed_add() -> Self {
        Self::EdAdd(EdAddTable)
    }
    pub fn embed<PF: PrimeCharacteristicRing>(&self) -> PF {
        PF::from_usize(self.index())
    }
    pub const fn index(&self) -> usize {
        unsafe { *(self as *const Self as *const usize) }
    }
}

impl TableT for Table {
    fn name(&self) -> &'static str {
        delegate_to_inner!(self, name)
    }
    fn table(&self) -> Table {
        delegate_to_inner!(self, table)
    }
    fn is_execution_table(&self) -> bool {
        delegate_to_inner!(self, is_execution_table)
    }
    fn bus_interactions(&self) -> Vec<BusInteraction> {
        delegate_to_inner!(self, bus_interactions)
    }
    fn padding_row(&self, zero_vec_ptr: usize, null_hash_ptr: usize, ending_pc: usize) -> Vec<PF<EF>> {
        delegate_to_inner!(self, padding_row, zero_vec_ptr, null_hash_ptr, ending_pc)
    }
    fn execute<M: MemoryAccess>(
        &self,
        arg_a: F,
        arg_b: F,
        arg_c: F,
        args: PrecompileCompTimeArgs<usize>,
        ctx: &mut InstructionContext<'_, M>,
    ) -> Result<(), RunnerError> {
        delegate_to_inner!(self, execute, arg_a, arg_b, arg_c, args, ctx)
    }
    fn n_columns_total(&self) -> usize {
        delegate_to_inner!(self, n_columns_total)
    }
}

impl Air for Table {
    type ExtraData = ();
    fn degree_air(&self) -> usize {
        delegate_to_inner!(self, degree_air)
    }
    fn n_columns(&self) -> usize {
        delegate_to_inner!(self, n_columns)
    }
    fn n_constraints(&self) -> usize {
        delegate_to_inner!(self, n_constraints)
    }
    fn n_shift_columns(&self) -> usize {
        delegate_to_inner!(self, n_shift_columns)
    }
    fn eval<AB: AirBuilder>(&self, _: &mut AB, _: &Self::ExtraData) {
        unreachable!()
    }
}

pub fn total_air_constraints() -> usize {
    ALL_TABLES.iter().map(|table| table.n_constraints()).sum()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_table_indices() {
        for (i, table) in ALL_TABLES.iter().enumerate() {
            assert_eq!(table.index(), i);
        }
    }

    /// Column-multiplicity buses first, then Multiplicity::One (the alpha-slot convention).
    #[test]
    fn test_column_buses_first() {
        for table in ALL_TABLES {
            let buses = table.bus_interactions();
            let k = n_column_buses(&buses);
            for (i, bus) in buses.iter().enumerate() {
                assert_eq!(matches!(bus.multiplicity, BusMultiplicity::Column(_)), i < k, "{}: bus {i}", table.name());
            }
        }
    }

    #[test]
    fn test_max_bus_width() {
        let expected_max_bus_width = ALL_TABLES
            .iter()
            .flat_map(|table| table.bus_interactions())
            .map(|bus| bus.data.len() + 1)
            .max()
            .unwrap();
        assert!(expected_max_bus_width <= MAX_BUS_WIDTH, "widest bus {expected_max_bus_width} > MAX_BUS_WIDTH");
        assert!(N_INSTRUCTION_COLUMNS + 2 <= MAX_BUS_WIDTH);
    }
}
