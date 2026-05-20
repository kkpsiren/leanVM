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
}
