//! Oracles: properties the compiler must satisfy, each turning a program (and its witnesses)
//! into a list of [`crate::triage::Finding`]s.
//!
//! - [`check_enforced`] — the core runtime property: emitted checks must be enforced.
//! - [`structural`] — the emitted bytecode must contain the recognizable lowering of each
//!   range check / panic / debug-assert (catches drops that runtime can mask).
//! - [`structural_diff`] — removing any emitted `assert` must change the bytecode (catches
//!   drops even for checks no witness can violate). Run only on the base program (`deep`),
//!   since it recompiles once per assert.

pub mod check_enforced;
pub mod structural;
pub mod structural_diff;

use crate::harness::{CompileOutcome, compile_source};
use crate::model::CheckedProgram;
use crate::rng::Rng;
use crate::triage::{Finding, FindingKind};

/// Compile a program once and run every oracle against it. This is the per-program entry point
/// the campaign uses. `deep` additionally runs the (more expensive) structural-diff oracle; the
/// campaign enables it for base programs but not for metamorphic variants.
#[must_use]
pub fn evaluate(prog: &CheckedProgram, rng: &mut Rng, seed: u64, deep: bool) -> Vec<Finding> {
    let source = prog.emit_source();

    let bc = match compile_source(&source) {
        CompileOutcome::Ok(bc) => bc,
        CompileOutcome::Panicked(p) => {
            return vec![Finding::new(
                FindingKind::CompilerPanic,
                seed,
                format!("compiler panicked: {} (at {:?})", p.message, p.location),
                source,
            )];
        }
        CompileOutcome::Rejected(e) => {
            return vec![Finding::new(
                FindingKind::CompileRejected,
                seed,
                format!("compiler rejected a generated program: {e}"),
                source,
            )];
        }
    };

    let mut findings = structural::evaluate(prog, &bc, seed, &source);
    if deep {
        findings.extend(structural_diff::evaluate(&bc, &source, seed));
    }
    findings.extend(check_enforced::evaluate(prog, &bc, &source, rng, seed));
    findings
}
