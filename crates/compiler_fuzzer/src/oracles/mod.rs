//! Oracles: properties the compiler must satisfy, each turning a program (and its witnesses)
//! into a list of [`crate::triage::Finding`]s.
//!
//! - [`check_enforced`] — the core runtime property: emitted checks must be enforced.
//! - [`structural`] — the emitted bytecode must contain the recognizable lowering of each
//!   range check / panic / debug-assert (catches drops that runtime can mask).

pub mod check_enforced;
pub mod structural;

use crate::harness::{CompileOutcome, compile_source};
use crate::model::CheckedProgram;
use crate::rng::Rng;
use crate::triage::{Finding, FindingKind};

/// Compile a program once and run every oracle against it. This is the per-program entry point
/// the campaign uses.
#[must_use]
pub fn evaluate(prog: &CheckedProgram, rng: &mut Rng, seed: u64) -> Vec<Finding> {
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
    findings.extend(check_enforced::evaluate(prog, &bc, &source, rng, seed));
    findings
}
