//! Bytecode-structural oracle: the emitted bytecode must *contain* the recognizable lowering
//! of each check the source declares.
//!
//! This complements the runtime oracle. A range check (`<` / `<=`) carries a prover-side
//! `debug_assert` companion that fires first at runtime, so dropping the actual range-check
//! *constraint* (the `DerefHint`s) can be invisible to a runtime test. Counting the lowering in
//! the bytecode catches that: every `<` / `<=` must leave behind exactly one inequality
//! companion (`Hint::DebugAssert { preceds_runtime_inequality: true, .. }`) and its deref
//! hints.

use lean_vm::{Bytecode, Hint};

use crate::model::{CheckedProgram, GadgetKind};
use crate::triage::{Finding, FindingKind};

/// Counts of the recognizable check lowerings present in a bytecode.
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub struct Lowerings {
    /// `Hint::DerefHint` occurrences (range-check derefs).
    pub deref_hints: usize,
    /// `Hint::DebugAssert` with `preceds_runtime_inequality == true` (one per `<` / `<=`).
    pub inequality_companions: usize,
    /// `Hint::DebugAssert` with `preceds_runtime_inequality == false` (explicit `debug_assert`).
    pub debug_asserts: usize,
    /// `Hint::Panic` occurrences (`assert False`).
    pub panics: usize,
}

/// Tally the check lowerings in a compiled bytecode.
#[must_use]
pub fn count_lowerings(bc: &Bytecode) -> Lowerings {
    let mut c = Lowerings::default();
    for entry in &bc.code {
        for hint in entry.hints.iter() {
            match hint {
                Hint::DerefHint { .. } => c.deref_hints += 1,
                Hint::DebugAssert {
                    preceds_runtime_inequality,
                    ..
                } => {
                    if *preceds_runtime_inequality {
                        c.inequality_companions += 1;
                    } else {
                        c.debug_asserts += 1;
                    }
                }
                Hint::Panic { .. } => c.panics += 1,
                _ => {}
            }
        }
    }
    c
}

/// Number of `<` / `<=` checks the program's source declares.
#[must_use]
pub fn expected_range_checks(prog: &CheckedProgram) -> usize {
    prog.gadgets
        .iter()
        .filter(|g| matches!(g.kind, GadgetKind::RangeLt { .. } | GadgetKind::RangeLe { .. }))
        .count()
}

/// Evaluate the structural property: at least one inequality companion per range check must
/// survive, and if there are range checks there must be deref hints.
#[must_use]
pub fn evaluate(prog: &CheckedProgram, bc: &Bytecode, seed: u64, source: &str) -> Vec<Finding> {
    let mut findings = Vec::new();
    let n_range = expected_range_checks(prog);
    let counts = count_lowerings(bc);

    if counts.inequality_companions < n_range {
        findings.push(Finding::new(
            FindingKind::MissingLowering,
            seed,
            format!(
                "expected {n_range} range-check companions, found {} (a `<`/`<=` lowering was dropped)",
                counts.inequality_companions
            ),
            source,
        ));
    }
    if n_range > 0 && counts.deref_hints == 0 {
        findings.push(Finding::new(
            FindingKind::MissingLowering,
            seed,
            format!("{n_range} range checks in source but no DerefHints in bytecode"),
            source,
        ));
    }

    findings
}
