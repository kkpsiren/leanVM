//! Self-tests for the fuzzer itself + a bounded clean-run baseline that participates in
//! `cargo testall`.
//!
//! The most important test is the *negative control* (`detects_dropped_check`): it proves the
//! oracle actually fires when a check is missing. Without it, "0 findings" could just mean the
//! oracle is blind.

use std::time::Duration;

use crate::campaign::{CampaignConfig, run_campaign};
use crate::field_util::{ExtMode, ExtOp, zero_public_input};
use crate::generators::{GenConfig, gen_const_fold, gen_program};
use crate::harness::{CompileOutcome, RunOutcome, compile_source, run};
use crate::model::{CheckedProgram, Computation, Gadget, GadgetKind, Op, Operand, Step};
use crate::rng::Rng;
use crate::subprocess::{SubprocessOutcome, compile_in_subprocess};

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
    let bin = super::fuzz_bin();
    let good = "from snark_lib import *\ndef main():\n    x = 1\n    assert x == 1\n    return\n";
    let bad = "@@@ this is not valid zkDSL @@@\n";
    let lim = 2 << 30;
    let timeout = Duration::from_secs(60);

    assert_eq!(
        compile_in_subprocess(&bin, good, timeout, lim).unwrap(),
        SubprocessOutcome::Compiled
    );
    assert_eq!(
        compile_in_subprocess(&bin, bad, timeout, lim).unwrap(),
        SubprocessOutcome::Rejected
    );
}

/// Teeth for the structural-diff oracle: a const-true `assert 5 == 5` folds to zero
/// instructions, so removing it leaves the bytecode unchanged and must be flagged; a runtime
/// `assert p[0] == p[1]` emits an instruction, so removing it changes the bytecode and must not
/// be flagged.
#[test]
fn structural_diff_flags_no_instruction_assert_only() {
    let src =
        "from snark_lib import *\ndef main():\n    p = 0\n    assert 5 == 5\n    assert p[0] == p[1]\n    return\n";
    let bc = match compile_source(src) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("compile failed: {other:?}"),
    };
    let findings = crate::oracles::structural_diff::evaluate(&bc, src, 0);
    let details: Vec<_> = findings.iter().map(|f| f.detail.clone()).collect();
    assert_eq!(
        findings.len(),
        1,
        "exactly the const-true assert should be flagged, got {details:?}"
    );
    assert!(
        findings[0].detail.contains("5 == 5"),
        "flagged the wrong assert: {}",
        findings[0].detail
    );
}

/// Soundness invariant (audit-verified): an out-of-range `match_range` dispatch must be REJECTED,
/// not silently skipped. Match arms (and the post-match region) are padded with `Panic`, and the
/// VM bounds-checks `pc`, so a selector past the last arm cannot fall through to skip a check. This
/// is the property that keeps `match` / `match_range` sound under prover-chosen selectors; if a
/// future change removes the padding this test catches it.
#[test]
fn match_range_out_of_range_is_rejected() {
    // NB: keep this on one physical line — a `\`-continuation would strip the leading whitespace
    // and break the significant indentation.
    let src = "from snark_lib import *\ndef fz_sq(n):\n    return n * n\ndef main():\n    buf = Array(2)\n    hint_witness(\"fuzz\", buf)\n    sel = buf[0]\n    res = match_range(sel, range(0, 3), lambda i: fz_sq(i))\n    assert res == buf[1]\n    return\n";
    let bc = match compile_source(src) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("compile failed: {other:?}"),
    };
    let input = zero_public_input();
    // In-range honest selector (sel = 2 ⇒ res = 4) passes.
    assert!(matches!(
        run(&bc, &input, &CheckedProgram::witness(&[vec![2, 4]])),
        RunOutcome::Ok(_)
    ));
    // Out-of-range selector (sel = 5, past the last arm) must be rejected regardless of the
    // expected value — the dispatch hits a Panic / pc-out-of-bounds before any check is skipped.
    for sel in [3u64, 5, 100] {
        assert!(
            !matches!(
                run(&bc, &input, &CheckedProgram::witness(&[vec![sel, 0]])),
                RunOutcome::Ok(_)
            ),
            "out-of-range match_range selector {sel} was accepted (skipped its check)"
        );
    }
}

/// The structural oracle assumes each `<` / `<=` lowers to exactly one inequality companion and
/// two `DerefHint`s, and that DerefHints come from nothing else. Lock that invariant in: if the
/// compiler ever changes range-check lowering, this breaks and the `2 * n_range` bound in
/// `oracles::structural` must be revisited.
#[test]
fn structural_counts_match_range_check_lowering() {
    let prog = CheckedProgram::new(vec![
        Gadget {
            id: 0,
            kind: GadgetKind::RangeLt { bound: 1000 },
            comp: Computation::identity(1),
        },
        Gadget {
            id: 1,
            kind: GadgetKind::RangeLe { bound: 1000 },
            comp: Computation::identity(1),
        },
        // A non-range gadget must contribute zero DerefHints / companions.
        Gadget {
            id: 2,
            kind: GadgetKind::EqBound,
            comp: Computation::identity(2),
        },
    ]);
    let bc = match compile_source(&prog.emit_source()) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("compile failed: {other:?}"),
    };
    let counts = crate::oracles::structural::count_lowerings(&bc);
    assert_eq!(
        counts.inequality_companions, 2,
        "expected one companion per range check"
    );
    assert_eq!(
        counts.deref_hints, 4,
        "expected two DerefHints per range check (and none elsewhere)"
    );
    // And the oracle is clean on a correctly-compiled program.
    assert!(crate::oracles::structural::evaluate(&prog, &bc, 0, &prog.emit_source()).is_empty());
}

/// The generator must actually emit every hard lowering construct over a modest seed range —
/// otherwise "0 findings" could just mean a construct is never generated.
#[test]
fn generator_covers_hard_constructs() {
    let mut all = String::new();
    let cfg = GenConfig::default();
    for seed in 0..400u64 {
        all.push_str(&gen_program(&mut Rng::new(seed), &cfg).emit_source());
    }
    for needle in [
        "match_range(",              // match expansion
        "for g",                     // range loop
        "fz_id(",                    // @inline expansion
        "hint_div_floor(",           // custom hint + constrain
        "!=",                        // inequality
        " < ",                       // range check
        "if g",                      // control flow
        " + 0",                      // copy-propagation pattern (CopyPropEq / inline)
        "_t2 = ",                    // CSE pair (CseEq)
        "_b0 = ",                    // running chain
        "poseidon16_compress_half(", // Poseidon2 compression precompile (Poseidon gadget)
        "dot_product_ee(",           // extension-field precompile (ExtOp Dot/Ee)
        "poly_eq_",                  // ext-op poly_eq family
        "_be(",                      // ext-op base-field-operand mode (add_be/dot_product_be/poly_eq_be)
        "_sel = ",                   // nested if-in-loop / IfThen / IfElse
        "* 2 + ",                    // bit-decomposition reconstruction (BitDecomp)
        "assert False",              // conditional panic (Panic)
        "debug_assert(",             // prover-side debug_assert (DebugAssertLt)
        "else:",                     // if/else (IfElse)
        " += ",                      // compound assignment (CompoundAssign)
        " / ",                       // runtime division (Div)
        "fz_pair(",                  // multi-value return + unpack (MultiReturn)
        "Array(8)",                  // pointer-offset filler array (PointerOffset)
        "parallel_range(",           // parallel loop (ParallelLoop)
        "saturating_sub(",           // const-fold built-in
        "next_multiple_of(",         // const-fold built-in
        "log2_ceil(",                // const-fold built-in
        " ** ",                      // const-fold exponent
    ] {
        assert!(all.contains(needle), "generator never emitted `{needle}`");
    }
}

/// Every gadget kind, with representative parameters — the full isolation matrix. Each must
/// compile, accept its honest witness, and reject *every* single-check violation in isolation.
/// This is the primary regression guard for new gadgets: a wrong honest/violating model, a bad
/// reference computation (ext-op, const-fold, division), or a non-isolating perturbation fails it.
fn all_gadget_kinds() -> Vec<GadgetKind> {
    let mut kinds = vec![
        GadgetKind::EqBound,
        GadgetKind::EqConst { c: 1_234_567 },
        GadgetKind::Ne,
        GadgetKind::Bool,
        GadgetKind::RangeLt { bound: 1000 },
        GadgetKind::RangeLe { bound: 1000 },
        // The 2^16 soundness boundary: `< 2^16` and `<= 2^16 - 1` are the largest sound bounds; the
        // violating value (== bound) must still be rejected via the `bound-1-value` deref.
        GadgetKind::RangeLt { bound: 1 << 16 },
        GadgetKind::RangeLe { bound: (1 << 16) - 1 },
        GadgetKind::UnrolledRangeLt { n: 4, bound: 1000 },
        GadgetKind::IfThen,
        GadgetKind::Loop,
        GadgetKind::MatchDispatch { m: 5 },
        GadgetKind::MatchChained,
        GadgetKind::InlineWrapped,
        GadgetKind::HintDiv { d: 7 },
        GadgetKind::CopyPropEq,
        GadgetKind::CseEq,
        GadgetKind::TwoReadsEq,
        GadgetKind::RunningChain { len: 4 },
        GadgetKind::NestedIfLoop { n: 3 },
        GadgetKind::NestedMutLoop { outer: 3, inner: 2 },
        GadgetKind::NestedMutLoop { outer: 1, inner: 1 },
        GadgetKind::BitDecomp { n: 6 },
        GadgetKind::Panic,
        GadgetKind::DebugAssertLt { bound: 1000 },
        GadgetKind::IfElse,
        GadgetKind::CompoundAssign,
        GadgetKind::Div,
        GadgetKind::MultiReturn,
        GadgetKind::PointerOffset,
        GadgetKind::PointerOffsetSub,
        GadgetKind::Poseidon,
        GadgetKind::ParallelLoop { n: 3 },
        GadgetKind::ForwardDeclEq,
    ];
    // Every extension-op (operation × mode) at lengths 1, 2, and the odd length 3 — validates the
    // reference math and the backward-accumulation/stride at an odd n.
    for op in [ExtOp::Add, ExtOp::Dot, ExtOp::PolyEq] {
        for mode in [ExtMode::Ee, ExtMode::Be] {
            for n in [1, 2, 3] {
                kinds.push(GadgetKind::ExtOp { op, mode, n });
            }
        }
    }
    // A few const-fold expressions (deterministic, exercises every const built-in).
    for seed in 0..6u64 {
        let (src, value) = gen_const_fold(&mut Rng::new(seed));
        kinds.push(GadgetKind::ConstFold { src, value });
    }
    kinds
}

fn comp_for(kind: &GadgetKind) -> Computation {
    match kind {
        // Comp-driven kinds get a small computation; the rest ignore it.
        GadgetKind::EqBound
        | GadgetKind::EqConst { .. }
        | GadgetKind::Ne
        | GadgetKind::IfThen
        | GadgetKind::IfElse
        | GadgetKind::InlineWrapped => Computation::identity(2),
        GadgetKind::Loop => Computation::identity(3),
        _ => Computation::identity(1),
    }
}

#[test]
fn hard_kinds_isolate() {
    let gadgets: Vec<Gadget> = all_gadget_kinds()
        .into_iter()
        .enumerate()
        .map(|(id, kind)| {
            let comp = comp_for(&kind);
            Gadget { id, kind, comp }
        })
        .collect();
    let prog = CheckedProgram::new(gadgets);
    let bc = match compile_source(&prog.emit_source()) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("all-kinds program failed to compile: {other:?}\n{}", prog.emit_source()),
    };
    let mut rng = Rng::new(3);
    let honest = prog.honest_buffers(&mut rng);
    let input = zero_public_input();
    assert!(
        matches!(run(&bc, &input, &CheckedProgram::witness(&honest)), RunOutcome::Ok(_)),
        "honest witness must pass for the all-kinds program"
    );
    // Break each independent check of each gadget in isolation; all must be rejected.
    for (i, g) in prog.gadgets.iter().enumerate() {
        for k in 0..g.n_violations() {
            let bufs = prog.violating_buffers(&honest, i, k);
            assert!(
                !matches!(run(&bc, &input, &CheckedProgram::witness(&bufs)), RunOutcome::Ok(_)),
                "violation #{k} for {} was accepted (check not enforced)",
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
        iterations: 64,
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
