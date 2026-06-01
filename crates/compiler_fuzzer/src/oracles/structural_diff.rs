//! Compile-time differential oracle: every emitted `assert` must produce *some* bytecode.
//!
//! For each `assert` line in the generated source, recompile the program with exactly that line
//! removed. If the resulting bytecode is byte-for-byte identical (same instruction hash), the
//! assert contributed **no instructions** — i.e. it was compiled away. That is a dropped check.
//!
//! This complements [`super::check_enforced`] (the runtime differential): it needs no witness,
//! works for every comparison kind, and — most importantly — covers checks that *cannot* be
//! violated by a witness because an honest runner always satisfies them (e.g. a
//! `hint_div_floor` correctness assert `q*D + r == a`). The runtime oracle is blind to those;
//! this one is not.
//!
//! Soundness of the signal relies on the generator only ever emitting *runtime-meaningful*
//! asserts (no `assert 5 == 5`-style constant tautologies, which the compiler legitimately folds
//! to nothing, and no `debug_assert`, which is prover-only and emits no instruction). The
//! gadget generators uphold this: every asserted relation is bound to a hint value.

use lean_vm::Bytecode;

use crate::harness::{CompileOutcome, compile_source};
use crate::triage::{Finding, FindingKind};

/// Re-compile `source` with each `assert` line removed in turn; flag any whose removal leaves
/// the instruction hash unchanged. `full_bc` is the bytecode of the unmodified `source`.
#[must_use]
pub fn evaluate(full_bc: &Bytecode, source: &str, seed: u64) -> Vec<Finding> {
    let mut findings = Vec::new();
    let lines: Vec<&str> = source.lines().collect();

    for (idx, line) in lines.iter().enumerate() {
        let trimmed = line.trim_start();
        // Real verifier-enforced asserts only. `debug_assert` is prover-only (no instruction);
        // an assert that is the sole statement of a block can't be removed without breaking the
        // block — those simply recompile to a clean error below and are skipped.
        if !trimmed.starts_with("assert ") {
            continue;
        }

        let mut variant = String::with_capacity(source.len());
        for (j, l) in lines.iter().enumerate() {
            if j == idx {
                continue;
            }
            variant.push_str(l);
            variant.push('\n');
        }

        match compile_source(&variant) {
            CompileOutcome::Ok(vbc) => {
                if vbc.hash == full_bc.hash {
                    findings.push(Finding::new(
                        FindingKind::DroppedCheck,
                        seed,
                        format!("removing `{trimmed}` left the bytecode hash unchanged — the assert emitted no instructions (dropped check)"),
                        source,
                    ));
                }
            }
            // Removing the assert made the program panic the compiler — itself a bug.
            CompileOutcome::Panicked(p) => findings.push(Finding::new(
                FindingKind::CompilerPanic,
                seed,
                format!("compiler panicked after removing `{trimmed}`: {}", p.message),
                source,
            )),
            // Removing the assert made the program invalid (e.g. emptied a block); not a signal.
            CompileOutcome::Rejected(_) => {}
        }
    }

    findings
}
