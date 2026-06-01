//! Self-tests for the fuzzer itself + a bounded clean-run baseline that participates in
//! `cargo testall`.
//!
//! The most important test is the *negative control* (`detects_dropped_check`): it proves the
//! oracle actually fires when a check is missing. Without it, "0 findings" could just mean the
//! oracle is blind.

use std::path::Path;
use std::time::Duration;

use compiler_fuzzer::campaign::{CampaignConfig, run_campaign};
use compiler_fuzzer::field_util::zero_public_input;
use compiler_fuzzer::generators::{GenConfig, gen_program};
use compiler_fuzzer::harness::{CompileOutcome, RunOutcome, compile_source, run};
use compiler_fuzzer::model::{CheckedProgram, Computation, Gadget, GadgetKind, Op, Operand, Step};
use compiler_fuzzer::rng::Rng;
use compiler_fuzzer::subprocess::{SubprocessOutcome, compile_in_subprocess};

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
    let violating = prog.violating_buffers(&honest, 0, 0);
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

/// The out-of-process compiler runner correctly classifies a clean compile and a clean
/// rejection. This proves the crash-probe machinery works without depending on any compiler
/// bug being present (so it is stable across compiler fixes).
#[test]
fn subprocess_classifies_clean_outcomes() {
    let bin = Path::new(env!("CARGO_BIN_EXE_compiler_fuzz"));
    let good = "from snark_lib import *\ndef main():\n    x = 1\n    assert x == 1\n    return\n";
    let bad = "@@@ this is not valid zkDSL @@@\n";
    let lim = 2 << 30;
    let timeout = Duration::from_secs(60);

    assert_eq!(
        compile_in_subprocess(bin, good, timeout, lim).unwrap(),
        SubprocessOutcome::Compiled
    );
    assert_eq!(
        compile_in_subprocess(bin, bad, timeout, lim).unwrap(),
        SubprocessOutcome::Rejected
    );
}

/// The generator must actually emit every hard lowering construct over a modest seed range —
/// otherwise "0 findings" could just mean a construct is never generated.
#[test]
fn generator_covers_hard_constructs() {
    let mut all = String::new();
    let cfg = GenConfig::default();
    for seed in 0..200u64 {
        all.push_str(&gen_program(&mut Rng::new(seed), &cfg).emit_source());
    }
    for needle in [
        "match_range(",    // match expansion
        "for g",           // range loop
        "fz_id(",          // @inline expansion
        "hint_div_floor(", // custom hint + constrain
        "!=",              // inequality
        " < ",             // range check
        "if g",            // control flow
        " + 0",            // copy-propagation pattern (CopyPropEq / inline)
        "_t2 = ",          // CSE pair (CseEq)
        "_b0 = ",          // running chain
        "dot_product_ee(", // extension-field precompile (ExtMulEq)
        "_sel = ",         // nested if-in-loop (NestedIfLoop) / IfThen
    ] {
        assert!(all.contains(needle), "generator never emitted `{needle}`");
    }
}

/// Each of the harder-lowering gadget kinds must compile, accept its honest witness, and reject
/// each single-gadget violation — independently and in isolation.
#[test]
fn hard_kinds_isolate() {
    let gadgets = vec![
        Gadget {
            id: 0,
            kind: GadgetKind::IfThen,
            comp: Computation::identity(2),
        },
        Gadget {
            id: 1,
            kind: GadgetKind::Loop,
            comp: Computation::identity(3),
        },
        Gadget {
            id: 2,
            kind: GadgetKind::MatchDispatch { m: 5 },
            comp: Computation::identity(1),
        },
        Gadget {
            id: 3,
            kind: GadgetKind::InlineWrapped,
            comp: Computation::identity(2),
        },
        Gadget {
            id: 4,
            kind: GadgetKind::HintDiv { d: 7 },
            comp: Computation::identity(1),
        },
        // Fusion/CSE/copy-prop targets (the check-dropping suspects).
        Gadget {
            id: 5,
            kind: GadgetKind::CopyPropEq,
            comp: Computation::identity(1),
        },
        Gadget {
            id: 6,
            kind: GadgetKind::CseEq,
            comp: Computation::identity(1),
        },
        Gadget {
            id: 7,
            kind: GadgetKind::TwoReadsEq,
            comp: Computation::identity(1),
        },
        Gadget {
            id: 8,
            kind: GadgetKind::RunningChain { len: 4 },
            comp: Computation::identity(1),
        },
        Gadget {
            id: 9,
            kind: GadgetKind::ExtMulEq,
            comp: Computation::identity(1),
        },
        Gadget {
            id: 10,
            kind: GadgetKind::NestedIfLoop { n: 3 },
            comp: Computation::identity(1),
        },
    ];
    let prog = CheckedProgram::new(gadgets);
    let bc = match compile_source(&prog.emit_source()) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!(
            "hard-kinds program failed to compile: {other:?}\n{}",
            prog.emit_source()
        ),
    };
    let mut rng = Rng::new(3);
    let honest = prog.honest_buffers(&mut rng);
    let input = zero_public_input();
    assert!(
        matches!(run(&bc, &input, &CheckedProgram::witness(&honest)), RunOutcome::Ok(_)),
        "honest witness must pass for the hard-kinds program"
    );
    // Break each independent check of each gadget in isolation; all must be rejected.
    for (i, g) in prog.gadgets.iter().enumerate() {
        for k in 0..g.n_violations() {
            let bufs = prog.violating_buffers(&honest, i, k);
            assert!(
                !matches!(run(&bc, &input, &CheckedProgram::witness(&bufs)), RunOutcome::Ok(_)),
                "violation #{k} for {} was accepted",
                g.label()
            );
        }
    }
}

/// Bounded baseline: the real compiler must produce no Critical/High findings over a fixed seed
/// range. This is the regression guard that runs as part of the suite.
#[test]
fn baseline_campaign_is_clean() {
    // A modest, fast regression guard (the real hunting is the CLI soak driver). Metamorphic
    // variants are on by default, so this exercises reorder/duplicate transforms too.
    let cfg = CampaignConfig {
        start_seed: 0,
        iterations: 128,
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
