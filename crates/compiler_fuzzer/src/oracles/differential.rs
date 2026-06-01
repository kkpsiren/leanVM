//! Random-differential oracle: the VM's accept/reject must match the reference model on *every*
//! witness, not just the one honest buffer and the hand-picked violating cells.
//!
//! The runtime oracle ([`super::check_enforced`]) runs one honest witness and perturbs only each
//! gadget's dedicated `exp` cell. That catches a *dropped* check, but an evil compiler can instead
//! *weaken* a check so it still rejects the canonical violating witness yet accepts some *other*
//! bad witness — an OR-escape (`assert a==b or a==0`), an implicit-zero collapse, a wrong-operand
//! binding, or a hidden free parameter. All of those survive a single-point test.
//!
//! This oracle closes that gap differentially: for every gadget whose acceptance is a pure
//! function of its buffer ([`Gadget::accepts`]), it splices many *random* buffers (plus honest
//! ones) into the gadget's slot and requires `VM-accept == reference-accept` for each. The
//! reference is the same exact model the honest buffers come from, so it is compiler-independent.
//! A single disagreement is a soundness finding. Gadgets with free selectors / runtime bases /
//! hint outputs return `None` from `accepts` and are skipped (their acceptance is not a pure
//! function of the buffer).

use lean_vm::Bytecode;

use crate::field_util::{rand_canonical, zero_public_input};
use crate::harness::{RunOutcome, run};
use crate::model::CheckedProgram;
use crate::rng::Rng;
use crate::triage::{Finding, FindingKind};

/// Random witnesses tested per (pure) gadget. Half honest (accept path), half uniformly random
/// (reject + escape-hatch path).
const WITNESSES_PER_GADGET: usize = 16;

/// Evaluate the differential property. `rng` drives the random witnesses, so a seed reproduces the
/// same probe set.
#[must_use]
pub fn evaluate(prog: &CheckedProgram, bc: &Bytecode, source: &str, rng: &mut Rng, seed: u64) -> Vec<Finding> {
    let mut findings = Vec::new();
    let honest = prog.honest_buffers(rng);
    let input = zero_public_input();

    for (i, g) in prog.gadgets.iter().enumerate() {
        // Only gadgets with a pure-function acceptance predicate participate.
        if g.accepts(&honest[i]).is_none() {
            continue;
        }
        for _ in 0..WITNESSES_PER_GADGET {
            let cand: Vec<u64> = if rng.flip() {
                g.honest_buffer(rng)
            } else {
                (0..g.buf_len()).map(|_| rand_canonical(rng)).collect()
            };
            let Some(expected_accept) = g.accepts(&cand) else {
                continue;
            };
            let mut bufs = honest.clone();
            bufs[i] = cand;
            // A panic counts as a reject for this property (the VM did not accept the witness).
            let got_accept = matches!(run(bc, &input, &CheckedProgram::witness(&bufs)), RunOutcome::Ok(_));
            if got_accept != expected_accept {
                let (kind, detail) = if got_accept {
                    (
                        FindingKind::DroppedCheck,
                        format!(
                            "differential: VM ACCEPTED a witness the spec REJECTS for {} — the \
                             constraint is weaker than the zkDSL (OR-escape / implicit-zero / wrong operand)",
                            g.label()
                        ),
                    )
                } else {
                    (
                        FindingKind::HonestRunFailed,
                        format!(
                            "differential: VM REJECTED a witness the spec ACCEPTS for {} — the \
                             constraint is stronger than the zkDSL (over-constrained)",
                            g.label()
                        ),
                    )
                };
                findings.push(
                    Finding::new(kind, seed, detail, source)
                        .with_gadget(i, g.check_kind().as_str())
                        .with_buffers(bufs),
                );
                break; // one finding per gadget is plenty
            }
        }
    }
    findings
}
