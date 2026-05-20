mod normal;
pub use normal::*;

mod packed;
pub use packed::*;

use field::Field;

pub trait AlphaPowers<EF> {
    fn alpha_powers(&self) -> &[EF];
}

impl<EF: Field> AlphaPowers<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers(&self) -> &[EF] {
        self
    }
}

pub trait AlphaPowersMut<EF> {
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF>;
}

impl<EF: Field> AlphaPowersMut<EF> for Vec<EF> {
    #[inline(always)]
    fn alpha_powers_mut(&mut self) -> &mut Vec<EF> {
        self
    }
}

/// Restricts which AIR assertions the constraint folder accumulates. Used by the
/// AIR sumcheck prover to evaluate the linear (degree-1) part of the AIR only twice
/// per row (z=0 and slope), while running the high-degree part once per z-point.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum FolderMode {
    /// Accumulate every assertion (default; used by simple callers / verifier).
    #[default]
    All,
    /// Skip `assert_zero_linear` (still bumps `constraint_index`). Used by the
    /// per-z high-degree evaluations.
    HighOnly,
    /// Only accumulate `assert_zero_linear`; every other assertion (including
    /// `assert_zero_ef` for the bus, `assert_eq_low`, and the entire
    /// `low_degree_block`) is skipped while still bumping `constraint_index`.
    LinearOnly,
    /// Only accumulate the bus (`assert_zero_ef` for fingerprint + `assert_zero`
    /// for multiplicity). Triggers `AirBuilder::bus_only() -> true` so each AIR's
    /// `eval` skips its column-claim iteration AND its high-degree AIR constraints
    /// (their expression compute is the costly part — not just the accumulator
    /// update). Sound only at round-0 z=0 of the AIR sumcheck, where the column
    /// values are actual table rows and every AIR constraint is zero by validity.
    BusOnly,
}
