//! Self-tests for the fuzzer itself + a bounded clean-run baseline that participates in
//! `cargo testall`.
//!
//! The most important test is the *negative control* (`detects_dropped_check`): it proves the
//! oracle actually fires when a check is missing. Without it, "0 findings" could just mean the
//! oracle is blind.

use compiler_fuzzer::campaign::{CampaignConfig, run_campaign};
use compiler_fuzzer::field_util::zero_public_input;
use compiler_fuzzer::generators::{GenConfig, gen_program};
use compiler_fuzzer::harness::{CompileOutcome, RunOutcome, compile_source, run};
use compiler_fuzzer::model::{CheckedProgram, Computation, Gadget, GadgetKind, Op, Operand, Step};
use compiler_fuzzer::rng::Rng;

fn one_eq_gadget_program() -> CheckedProgram {
    // value = in0 + in1 ; assert value == buf[2]
    let comp = Computation {
        n_inputs: 2,
        steps: vec![Step {
            op: Op::Add,
            a: Operand::Input(0),
            b: Operand::Input(1),
        }],
    };
    CheckedProgram::new(vec![Gadget {
        id: 0,
        kind: GadgetKind::EqBound,
        comp,
    }])
}

#[test]
fn reference_eval_matches_hand_computation() {
    // value = (in0 + in1) * in2
    let comp = Computation {
        n_inputs: 3,
        steps: vec![
            Step {
                op: Op::Add,
                a: Operand::Input(0),
                b: Operand::Input(1),
            },
            Step {
                op: Op::Mul,
                a: Operand::Temp(0),
                b: Operand::Input(2),
            },
        ],
    };
    assert_eq!(comp.eval(&[3, 4, 5]), 35);
    assert_eq!(comp.eval(&[0, 0, 9]), 0);
}

#[test]
fn emitter_is_deterministic() {
    let a = gen_program(&mut Rng::new(7), &GenConfig::default()).emit_source();
    let b = gen_program(&mut Rng::new(7), &GenConfig::default()).emit_source();
    assert_eq!(a, b, "same seed must emit identical source");
    assert!(a.contains("def main():"));
    assert!(a.contains("hint_witness(\"fuzz\""));
}

/// Teeth test: with the real check present a violating witness is rejected; with the check
/// neutralized (simulating a compiler that dropped it) the *same* violating witness is accepted
/// — which is exactly the `DroppedCheck` condition the oracle keys on.
#[test]
fn detects_dropped_check() {
    let prog = one_eq_gadget_program();
    let source = prog.emit_source();

    // Neutralize the single assertion into a tautology (the buffer layout is unchanged, so the
    // honest/violating witnesses still apply).
    assert!(source.contains("assert g0_t0 == g0_exp"));
    let broken = source.replace("assert g0_t0 == g0_exp", "assert g0_exp == g0_exp");

    let bc_good = match compile_source(&source) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("good program failed to compile: {other:?}"),
    };
    let bc_broken = match compile_source(&broken) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("neutralized program failed to compile: {other:?}"),
    };

    let mut rng = Rng::new(1);
    let honest = prog.honest_buffers(&mut rng);
    let violating = prog.violating_buffers(&honest, 0);
    let input = zero_public_input();

    // Honest witness passes on both.
    assert!(matches!(
        run(&bc_good, &input, &CheckedProgram::witness(&honest)),
        RunOutcome::Ok(_)
    ));
    assert!(matches!(
        run(&bc_broken, &input, &CheckedProgram::witness(&honest)),
        RunOutcome::Ok(_)
    ));

    // The violating witness is rejected with the check, accepted without it.
    assert!(
        matches!(
            run(&bc_good, &input, &CheckedProgram::witness(&violating)),
            RunOutcome::Error(_)
        ),
        "violating witness must be rejected when the check is present"
    );
    assert!(
        matches!(
            run(&bc_broken, &input, &CheckedProgram::witness(&violating)),
            RunOutcome::Ok(_)
        ),
        "violating witness must be accepted when the check is dropped — the oracle's signal"
    );
}

/// Bounded baseline: the real compiler must produce no Critical/High findings over a fixed seed
/// range. This is the regression guard that runs as part of the suite.
#[test]
fn baseline_campaign_is_clean() {
    let cfg = CampaignConfig {
        start_seed: 0,
        iterations: 256,
        ..Default::default()
    };
    let report = run_campaign(&cfg);
    let actionable: Vec<_> = report.actionable().map(|f| f.summary()).collect();
    assert!(
        actionable.is_empty(),
        "expected no Critical/High findings, got {}:\n{}",
        actionable.len(),
        actionable.join("\n")
    );
}
