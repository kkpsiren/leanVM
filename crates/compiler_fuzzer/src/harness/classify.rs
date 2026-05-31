//! Classification of execution failures, so an oracle can decide whether a given
//! `RunnerError` is *consistent* with a particular check firing (the basis for failure
//! isolation — see [`crate::oracles::check_enforced`]).

use lean_vm::RunnerError;

/// The kind of comparison a generated check enforces.
///
/// Mirrors `lean_vm::Boolean` but lives here so generators don't depend on VM internals,
/// and so we can attach the "which error variants prove this check fired" policy.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum CheckKind {
    /// `assert a == b` (and boolean asserts `assert x * (1 - x) == 0`).
    Eq,
    /// `assert a != b`.
    Ne,
    /// `assert a < b` (range check).
    Lt,
    /// `assert a <= b` (range check).
    Le,
    /// `assert False` / `assert False, "msg"`.
    Panic,
    /// `debug_assert(...)` (prover-side; the honest runner still enforces it).
    Debug,
}

impl CheckKind {
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Eq => "==",
            Self::Ne => "!=",
            Self::Lt => "<",
            Self::Le => "<=",
            Self::Panic => "assert False",
            Self::Debug => "debug_assert",
        }
    }
}

/// A coarse bucket for a `RunnerError`, abstracting away its payload.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FailureClass {
    /// Arithmetic-constraint mismatch (`NotEqual`). This is how `==`, `!=`, boolean asserts,
    /// and `assert False` (the `0 * fp == 1` computation) all surface.
    NotEqual,
    /// A range-check (`<` / `<=`) failed: the deref of an out-of-range address could not be
    /// resolved, or the bound exceeded `2^16`.
    RangeCheck,
    /// A `debug_assert(...)` condition was false at witness-generation time.
    DebugAssert,
    /// Reading memory that was never written.
    UndefinedMemory,
    /// Two different values written to the same write-once cell — usually a *collateral*
    /// failure, not the check we targeted.
    MemoryConflict,
    NonBooleanCondition,
    DivByZero,
    OutOfMemory,
    NotAPointer,
    PcOutOfBounds,
    InvalidExtensionOp,
    /// A `hint_witness` label was missing / exhausted / left unconsumed.
    HintWitness,
    /// A custom-hint argument was invalid (e.g. bad `chunk_size`).
    HintArgs,
    /// A parallel-loop segment failed; carries the inner class.
    Parallel(Box<FailureClass>),
}

impl FailureClass {
    #[must_use]
    pub fn of(err: &RunnerError) -> Self {
        match err {
            RunnerError::NotEqual(..) => Self::NotEqual,
            RunnerError::ImpossibleDerefResolution | RunnerError::RangeCheckWithTooBigRange { .. } => Self::RangeCheck,
            RunnerError::DebugAssertFailed(..) => Self::DebugAssert,
            RunnerError::UndefinedMemory(..) => Self::UndefinedMemory,
            RunnerError::MemoryAlreadySet { .. } => Self::MemoryConflict,
            RunnerError::NonBooleanJumpCondition(..) => Self::NonBooleanCondition,
            RunnerError::DivByZero => Self::DivByZero,
            RunnerError::OutOfMemory => Self::OutOfMemory,
            RunnerError::NotAPointer => Self::NotAPointer,
            RunnerError::PCOutOfBounds => Self::PcOutOfBounds,
            RunnerError::InvalidExtensionOp => Self::InvalidExtensionOp,
            RunnerError::InvalidHintWitness(..) => Self::HintWitness,
            RunnerError::InvalidHintArguments(..) => Self::HintArgs,
            RunnerError::ParallelSegmentFailed(_, inner) => Self::Parallel(Box::new(Self::of(inner))),
        }
    }

    /// Strip the `Parallel(..)` wrapper, if any — a check inside a `parallel_range` body
    /// surfaces wrapped, but the underlying class is what proves the check fired.
    #[must_use]
    pub fn unwrap_parallel(&self) -> &Self {
        match self {
            Self::Parallel(inner) => inner.unwrap_parallel(),
            other => other,
        }
    }

    /// Whether observing this failure is *consistent with* the given check having fired.
    ///
    /// The accepted classes per kind were determined empirically (see the crate's
    /// calibration), not assumed:
    /// - `==` (two memory cells) is enforced via write-once memory, so a violation surfaces
    ///   as `MemoryConflict`; when one side is a constant/fresh result it surfaces as
    ///   `NotEqual`. Both are accepted.
    /// - `!=` surfaces as `NotEqual` (the `(a-b)*inv == 1` constraint becomes `0 == 1`).
    /// - `<` / `<=` carry a prover-side `debug_assert` companion that fires *first*, so the
    ///   common surface is `DebugAssert`; if that were dropped, the range-check deref would
    ///   surface as `RangeCheck` / `UndefinedMemory`. A too-big bound is `RangeCheck`.
    /// - `assert False` lowers to the impossible computation `0 * fp == 1` → `NotEqual`.
    /// - `debug_assert(...)` → `DebugAssert`.
    ///
    /// This decides *diagnostic consistency* only. The check-enforcement oracle's bug
    /// verdict is driven by "honest passes but the violating witness was accepted", which is
    /// robust regardless of variant; an inconsistent variant is reported as inconclusive
    /// (possible non-isolated perturbation), never as a confirmed dropped check.
    #[must_use]
    pub fn consistent_with(&self, kind: CheckKind) -> bool {
        let c = self.unwrap_parallel();
        match kind {
            CheckKind::Eq => matches!(c, Self::NotEqual | Self::MemoryConflict),
            CheckKind::Ne | CheckKind::Panic => *c == Self::NotEqual,
            CheckKind::Lt | CheckKind::Le => matches!(c, Self::DebugAssert | Self::RangeCheck | Self::UndefinedMemory),
            CheckKind::Debug => *c == Self::DebugAssert,
        }
    }
}
