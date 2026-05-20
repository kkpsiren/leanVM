#![cfg_attr(not(test), warn(unused_crate_dependencies))]

use core::ops::{Add, Mul, Sub};
use field::{Algebra, PrimeCharacteristicRing};

mod symbolic;
pub use symbolic::*;

mod constraint_folder;
pub use constraint_folder::*;

pub trait Air: Send + Sync + 'static {
    type ExtraData: Send + Sync + 'static;

    fn degree_air(&self) -> usize;

    fn n_columns(&self) -> usize;

    fn n_constraints(&self) -> usize;

    /// Whether `eval` opens with an `assert_zero_ef(bus)` that consumes `alpha^0`.
    /// When `true`, the AIR's `assert_zero_linear` calls start at `alpha^1`, so the
    /// AIR sumcheck prover folds in column claims with `alpha^{1+j}`. When `false`
    /// (e.g. standalone AIR tests with `BUS=false`), the prover uses `alpha^{j}`.
    fn has_bus(&self) -> bool {
        false
    }

    /// Number of "shift" columns (the ones that are also queried at the next
    /// row). By convention they occupy columns `0..n_shift_columns()` of the
    /// table; the remaining columns are "flat" (queried at the current row only).
    fn n_shift_columns(&self) -> usize;

    fn eval<AB: AirBuilder>(&self, builder: &mut AB, extra_data: &Self::ExtraData);

    /// If the AIR contains a `low_degree_block` sub-region, returns `(degree, n_constraints)`
    fn low_degree_air(&self) -> Option<(usize, usize)> {
        None
    }

    /// Sorted committed column indices that `eval` accumulates via
    /// `assert_zero_linear` (degree-1, constant alpha indices `1..1 + len()` —
    /// alpha^0 is reserved for the bus).
    ///
    /// The AIR sumcheck prover uses this to compute the linear-degree contribution
    /// at a row via a direct dot product, instead of running the full `eval` once
    /// per z-point. Returning `&[]` means the AIR has no linear-folded constraints
    /// and the prover stays on the original code path.
    fn logup_claim_columns(&self) -> &'static [usize] {
        &[]
    }
}

pub trait AirBuilder: Sized {
    /// Always the base field (or its SIMD packing).
    type F: PrimeCharacteristicRing + 'static;
    /// Intermediate field: equals F in base-field rounds, EF in extension rounds
    /// (or their respective SIMD packings).
    type IF: Algebra<Self::F> + 'static;
    /// Always the extension field (or its SIMD packing).
    type EF: PrimeCharacteristicRing
        + 'static
        + Add<Self::IF, Output = Self::EF>
        + Mul<Self::IF, Output = Self::EF>
        + Add<Self::F, Output = Self::EF>
        + Mul<Self::F, Output = Self::EF>
        + Sub<Self::F, Output = Self::EF>
        + From<Self::F>;

    /// Current-row column evaluations ("flat" view).
    fn flat(&self) -> &[Self::IF];
    /// Next-row column evaluations, restricted to the first `n_shift_columns()`
    /// columns (the "shift" view).
    fn shift(&self) -> &[Self::IF];

    fn assert_zero(&mut self, x: Self::IF);
    fn assert_zero_ef(&mut self, x: Self::EF);

    /// Assert a degree-1 (linear in columns) constraint. The constraint-folder path
    /// uses this to keep linear constraints in a separate accumulator: per row, a
    /// linear constraint's contribution at z is `lin(z=0) + z·lin_slope` (by
    /// linearity), so two cheap evaluations suffice instead of one per z-point.
    /// Builders that don't take advantage of this fall back to `assert_zero`.
    fn assert_zero_linear(&mut self, x: Self::IF) {
        self.assert_zero(x);
    }

    fn assert_eq(&mut self, x: Self::IF, y: Self::IF) {
        self.assert_zero(x - y);
    }

    fn assert_bool(&mut self, x: Self::IF) {
        self.assert_zero(x.bool_check());
    }

    fn assert_eq_low(&mut self, x: Self::IF, y: Self::IF) {
        self.assert_eq(x, y);
    }

    /// Execute `block` as a low-degree sub-region whose post-state is "cacheable"
    /// = linear in z without the low-degree constraints
    fn low_degree_block<F>(&mut self, state: &mut [Self::IF], block: F)
    where
        F: FnOnce(&mut Self, &mut [Self::IF]),
    {
        block(self, state);
    }

    /// useful to build the recursion program
    #[inline(always)]
    fn declare_values(&mut self, values: &[Self::IF]) {
        let _ = values;
    }

    /// True when the constraint folder is in `BusOnly` mode (round-0 z=0 of the
    /// AIR sumcheck). The AIR's `eval` uses this to early-return after emitting
    /// the bus assertions — skipping the cost of computing every high-degree AIR
    /// constraint's expression, which evaluates to zero by AIR validity at that
    /// point. The default impl returns `false` (every other builder runs the
    /// full AIR).
    #[inline(always)]
    fn bus_only(&self) -> bool {
        false
    }
}
