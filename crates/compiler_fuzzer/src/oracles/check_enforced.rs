//! The core oracle: every check a program emits must be *enforced* at runtime.
//!
//! Given an already-compiled program built from independent gadgets:
//! 1. run the honest witness — it must pass (a failure means an over-zealous check, a
//!    miscompilation, or a generator bug, all worth surfacing);
//! 2. for each gadget, run a witness that violates *only that gadget's* check. It must be
//!    rejected. If it is **accepted**, the check was silently dropped during compilation — the
//!    critical bug class this crate exists to find.
//!
//! Because gadgets are independent and the honest baseline passes, a rejection on a single-
//! gadget perturbation is attributable to that gadget. The error *variant* is checked against
//! the gadget's kind for diagnostics; an inconsistent variant is reported as `Info` (a possible
//! non-isolated perturbation), never as a confirmed drop.

use lean_vm::Bytecode;

use crate::field_util::zero_public_input;
use crate::harness::{FailureClass, RunOutcome, run};
use crate::model::CheckedProgram;
use crate::rng::Rng;
use crate::triage::{Finding, FindingKind};

/// Evaluate the check-enforcement property for one already-compiled program. `rng` is used only
/// to build the honest witness, so the same seed reproduces the same buffers.
#[must_use]
pub fn evaluate(prog: &CheckedProgram, bc: &Bytecode, source: &str, rng: &mut Rng, seed: u64) -> Vec<Finding> {
    let mut findings = Vec::new();

    let honest = prog.honest_buffers(rng);
    let input = zero_public_input();

    match run(bc, &input, &CheckedProgram::witness(&honest)) {
        RunOutcome::Ok(_) => {}
        RunOutcome::Error(e) => {
            findings.push(
                Finding::new(
                    FindingKind::HonestRunFailed,
                    seed,
                    format!("honest witness was rejected: {e:?}"),
                    source,
                )
                .with_buffers(honest),
            );
            return findings;
        }
        RunOutcome::Panicked(p) => {
            findings.push(
                Finding::new(
                    FindingKind::HonestRunPanicked,
                    seed,
                    format!("VM panicked on honest witness: {}", p.message),
                    source,
                )
                .with_buffers(honest),
            );
            return findings;
        }
    }

    for (i, g) in prog.gadgets.iter().enumerate() {
        let check = g.check_kind();
        // A gadget may enforce several independent checks (CSE pairs, chain checkpoints, …);
        // break each one in isolation and require the VM to reject it.
        for k in 0..g.n_violations() {
            let bufs = prog.violating_buffers(&honest, i, k);
            match run(bc, &input, &CheckedProgram::witness(&bufs)) {
                RunOutcome::Ok(_) => findings.push(
                    Finding::new(
                        FindingKind::DroppedCheck,
                        seed,
                        format!("violating witness #{k} for {} was ACCEPTED — check dropped", g.label()),
                        source,
                    )
                    .with_gadget(i, check.as_str())
                    .with_buffers(bufs),
                ),
                RunOutcome::Error(e) => {
                    let cls = FailureClass::of(&e);
                    if !cls.consistent_with(check) {
                        findings.push(
                            Finding::new(
                                FindingKind::InconsistentVariant,
                                seed,
                                format!(
                                    "{} #{k} rejected with unexpected variant {e:?} (class {cls:?})",
                                    g.label()
                                ),
                                source,
                            )
                            .with_gadget(i, check.as_str())
                            .with_buffers(bufs),
                        );
                    }
                }
                RunOutcome::Panicked(p) => findings.push(
                    Finding::new(
                        FindingKind::ViolationPanicked,
                        seed,
                        format!("VM panicked on violating {} #{k}: {}", g.label(), p.message),
                        source,
                    )
                    .with_gadget(i, check.as_str())
                    .with_buffers(bufs),
                ),
            }
        }
    }

    findings
}
