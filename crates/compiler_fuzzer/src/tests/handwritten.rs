//! Handwritten faithfulness suite: incredibly tangled programs that each express a constraint and
//! must enforce it *soundly* in the emitted bytecode, no matter how the optimizer/lowering mangles
//! the path to it.
//!
//! For every case we assert three things:
//! 1. it compiles;
//! 2. **no emitted `assert` is compiled away** — removing any `assert` line must change the
//!    bytecode (the structural-diff oracle). This is the "the constraint is actually in the ISA"
//!    half of faithfulness;
//! 3. the **honest** witness is accepted and **every constraint-violating** witness is rejected.
//!    This is the "the constraint is the *right* one" half.
//!
//! The honest expected values are hand-computed where feasible, so a miscompiled computation also
//! trips the honest run. The witness is a single buffer consumed by one `hint_witness("w", w)`.
//!
//! These are deliberately gnarly: deep copy-prop/CSE/fusion chains, runtime-indexed derefs, nested
//! `if`/`elif`/`else`, nested `range` loops, `match_range` dispatch, nested `@inline`, bit
//! decomposition, extension-field precompiles, range checks, custom hints, and combinations of all
//! of the above — exactly where a sound compiler is hardest to get right.

use std::collections::HashMap;

use crate::field_util::{ExtMode, ExtOp, add_mod, div_canonical, ext_op_eval, f, sub_mod, zero_public_input};
use crate::harness::{CompileOutcome, RunOutcome, compile_source, run};
use lean_vm::{ExecutionWitness, F};

/// One buffer consumed under the label `"w"`.
fn witness_w(buf: &[u64]) -> ExecutionWitness {
    let mut hints = HashMap::new();
    hints.insert("w".to_string(), vec![buf.iter().map(|&v| f(v)).collect::<Vec<F>>()]);
    ExecutionWitness {
        hints,
        ..Default::default()
    }
}

/// Compile `source`, assert no `assert` was compiled to zero instructions, the honest witness is
/// accepted, and every violating witness is rejected.
fn assert_faithful(name: &str, source: &str, honest: &[u64], violations: &[(&str, Vec<u64>)]) {
    let bc = match compile_source(source) {
        CompileOutcome::Ok(bc) => bc,
        other => panic!("[{name}] failed to compile: {other:?}\n--- source ---\n{source}"),
    };

    // Faithfulness #1: every emitted assert must contribute instructions (none silently folded).
    let dropped = crate::oracles::structural_diff::evaluate(&bc, source, 0);
    assert!(
        dropped.is_empty(),
        "[{name}] an assert was compiled away (constraint not in the ISA): {:?}",
        dropped.iter().map(|f| f.detail.clone()).collect::<Vec<_>>()
    );

    // Faithfulness #2a: the honest witness is accepted.
    let input = zero_public_input();
    match run(&bc, &input, &witness_w(honest)) {
        RunOutcome::Ok(_) => {}
        other => panic!("[{name}] honest witness was NOT accepted: {other:?}\nhonest = {honest:?}"),
    }

    // Faithfulness #2b: every constraint-violating witness is rejected.
    for (desc, v) in violations {
        match run(&bc, &input, &witness_w(v)) {
            RunOutcome::Ok(_) => panic!(
                "[{name}] violating witness '{desc}' was ACCEPTED — the constraint is not faithfully \
                 enforced.\n  witness = {v:?}"
            ),
            RunOutcome::Error(_) => {}
            RunOutcome::Panicked(p) => panic!("[{name}] VM panicked on '{desc}': {}", p.message),
        }
    }
}

// --- 1. Copy-propagation chain: a long `+ 0` / alias chain must still bind w[0] == w[1]. ---
#[test]
fn copy_prop_chain() {
    let src = r#"from snark_lib import *
def main():
    w = Array(2)
    hint_witness("w", w)
    a = w[0]
    b = a + 0
    c = b + 0
    d = c + 0
    e = d + 0
    g = e + 0
    assert g == w[1]
    return
"#;
    assert_faithful("copy_prop_chain", src, &[7, 7], &[("g != exp", vec![7, 8])]);
}

// --- 2. CSE of three identical products, each asserted to its own cell ⇒ all three must hold. ---
#[test]
fn cse_triple_product() {
    let src = r#"from snark_lib import *
def main():
    w = Array(5)
    hint_witness("w", w)
    x = w[0]
    y = w[1]
    t1 = x * y
    t2 = x * y
    t3 = x * y
    assert t1 == w[2]
    assert t2 == w[3]
    assert t3 == w[4]
    return
"#;
    assert_faithful(
        "cse_triple_product",
        src,
        &[3, 5, 15, 15, 15],
        &[
            ("break e1", vec![3, 5, 16, 15, 15]),
            ("break e2", vec![3, 5, 15, 16, 15]),
            ("break e3", vec![3, 5, 15, 15, 16]),
        ],
    );
}

// --- 3. Assert-fusion chain: a fused `assert p == c` (⇒ c = a+b) must still feed the next check. ---
#[test]
fn assert_fusion_chain() {
    // p = a + b; assert p == c        (fuses to c = a + b)
    // q = c * d; assert q == a         (forces a == (a+b)*d)
    // honest: a=0,b=5,c=5,d=0 ⇒ p=5==c, q=5*0=0==a.
    let src = r#"from snark_lib import *
def main():
    w = Array(4)
    hint_witness("w", w)
    p = w[0] + w[1]
    assert p == w[2]
    q = w[2] * w[3]
    assert q == w[0]
    return
"#;
    assert_faithful(
        "assert_fusion_chain",
        src,
        &[0, 5, 5, 0],
        &[
            ("break first assert (c)", vec![0, 5, 6, 0]),
            ("break second assert (d⇒q≠a)", vec![0, 5, 5, 1]),
        ],
    );
}

// --- 4. const-offset-into-deref fold: arr[base + K] with runtime base, const K. ---
#[test]
fn const_offset_into_deref() {
    let src = r#"from snark_lib import *
def main():
    w = Array(10)
    hint_witness("w", w)
    arr = Array(8)
    for i in unroll(0, 8):
        arr[i] = w[i + 1]
    base = w[0]
    v = arr[base + 5]
    assert v == w[9]
    return
"#;
    // base=0 ⇒ v = arr[5] = w[6] = 15; exp = w[9] = 15.
    assert_faithful(
        "const_offset_into_deref",
        src,
        &[0, 10, 11, 12, 13, 14, 15, 16, 17, 15],
        &[("break exp", vec![0, 10, 11, 12, 13, 14, 15, 16, 17, 99])],
    );
}

// --- 5. Nested if/elif/else: the constraint lives after a forward decl assigned in every leaf. ---
#[test]
fn nested_if_elif_else() {
    let src = r#"from snark_lib import *
def main():
    w = Array(4)
    hint_witness("w", w)
    s1 = w[0]
    s2 = w[1]
    r: Imm
    if s1 == 0:
        if s2 == 0:
            r = w[2] + 1
        else:
            r = w[2] + 2
    elif s1 == 1:
        r = w[2] + 3
    else:
        r = w[2] + 4
    assert r == w[3]
    return
"#;
    // s1=0,s2=0 ⇒ r = w[2]+1 = 6.
    assert_faithful(
        "nested_if_elif_else",
        src,
        &[0, 0, 5, 6],
        &[("break exp", vec![0, 0, 5, 7])],
    );
}

// --- 6. range loop with a mutable accumulator + a per-iteration checkpoint assert. ---
#[test]
fn range_loop_running_checkpoints() {
    let src = r#"from snark_lib import *
def main():
    w = Array(8)
    hint_witness("w", w)
    acc = Array(4)
    acc[0] = w[0]
    assert acc[0] == w[4]
    for i in range(1, 4):
        acc[i] = acc[i - 1] + w[i]
        assert acc[i] == w[4 + i]
    return
"#;
    // b0=10, d=[1,2,3]; checkpoints 10,11,13,16.
    assert_faithful(
        "range_loop_running_checkpoints",
        src,
        &[10, 1, 2, 3, 10, 11, 13, 16],
        &[
            ("break c0", vec![10, 1, 2, 3, 99, 11, 13, 16]),
            ("break c2", vec![10, 1, 2, 3, 10, 11, 99, 16]),
            ("break c3", vec![10, 1, 2, 3, 10, 11, 13, 99]),
        ],
    );
}

// --- 7. Bit decomposition: prover-supplied bits, each constrained boolean, then reconstructed. ---
#[test]
fn bit_decomposition_and_reconstruction() {
    let src = r#"from snark_lib import *
def main():
    w = Array(9)
    hint_witness("w", w)
    acc: Mut = 0
    for i in unroll(0, 8):
        bit = w[i]
        assert bit * (bit - 1) == 0
        acc = acc * 2 + bit
    assert acc == w[8]
    return
"#;
    // bits 1,0,1,1,0,0,1,0 ⇒ value 178.
    assert_faithful(
        "bit_decomposition_and_reconstruction",
        src,
        &[1, 0, 1, 1, 0, 0, 1, 0, 178],
        &[
            // non-boolean bit (b0=2), reconstruction kept consistent (306) ⇒ only the boolean fails.
            ("non-boolean bit", vec![2, 0, 1, 1, 0, 0, 1, 0, 306]),
            // wrong reconstruction value.
            ("wrong value", vec![1, 0, 1, 1, 0, 0, 1, 0, 179]),
        ],
    );
}

// --- 8. Extension-field multiply: every one of the 5 result coordinates must match. ---
#[test]
fn extension_field_multiply() {
    let a = [1u64, 2, 3, 4, 5];
    let b = [6u64, 7, 8, 9, 10];
    let exp = ext_op_eval(ExtOp::Dot, ExtMode::Ee, &a, &b, 1);
    let mut honest: Vec<u64> = a.to_vec();
    honest.extend(b);
    honest.extend(exp);
    let mut viol = honest.clone();
    viol[12] += 1; // perturb result coordinate 2
    let src = r#"from snark_lib import *
def main():
    w = Array(15)
    hint_witness("w", w)
    res = Array(5)
    dot_product_ee(w, w + 5, res)
    for i in unroll(0, 5):
        assert res[i] == w[10 + i]
    return
"#;
    assert_faithful(
        "extension_field_multiply",
        src,
        &honest,
        &[("break result coord 2", viol)],
    );
}

// --- 9. Nested @inline functions: the constraint survives repeated inline expansion. ---
#[test]
fn nested_inline_expansion() {
    let src = r#"from snark_lib import *
@inline
def add1(x):
    return x + 1
@inline
def double(x):
    return x * 2
def main():
    w = Array(2)
    hint_witness("w", w)
    a = add1(w[0])
    b = double(a)
    c = add1(b)
    assert c == w[1]
    return
"#;
    // c = 2*(w0+1)+1 = 2*w0 + 3 ; w0=10 ⇒ 23.
    assert_faithful(
        "nested_inline_expansion",
        src,
        &[10, 23],
        &[("break exp", vec![10, 24])],
    );
}

// --- 10. match_range dispatch to a const-parameter function. ---
#[test]
fn match_range_dispatch() {
    let src = r#"from snark_lib import *
def sq(n: Const):
    return n * n
def main():
    w = Array(2)
    hint_witness("w", w)
    sel = w[0]
    r = match_range(sel, range(0, 6), lambda i: sq(i))
    assert r == w[1]
    return
"#;
    // sel=4 ⇒ r=16.
    assert_faithful("match_range_dispatch", src, &[4, 16], &[("break exp", vec![4, 17])]);
}

// --- 11. The gauntlet: copy-prop ⇒ CSE ⇒ fusion ⇒ loop accumulator, all feeding three asserts. ---
#[test]
fn pass_gauntlet() {
    let src = r#"from snark_lib import *
def main():
    w = Array(5)
    hint_witness("w", w)
    x = w[0]
    y = w[1]
    a = x + 0
    b = y + 0
    p1 = a * b
    p2 = a * b
    assert p1 == w[2]
    q = a + b
    assert q == w[3]
    acc = Array(3)
    acc[0] = p2
    for i in range(0, 2):
        acc[i + 1] = acc[i] + w[2]
    assert acc[2] == w[4]
    return
"#;
    // x=3,y=5 ⇒ p=15, q=8, acc = 15 + 2*15 = 45.
    assert_faithful(
        "pass_gauntlet",
        src,
        &[3, 5, 15, 8, 45],
        &[
            ("break p1 (and acc)", vec![3, 5, 16, 8, 45]),
            ("break q only", vec![3, 5, 15, 9, 45]),
            ("break acc only", vec![3, 5, 15, 8, 46]),
        ],
    );
}

// --- 12. Range checks (`<` and `<=`) with distinct bounds; out-of-range must be rejected. ---
#[test]
fn range_checks_distinct_bounds() {
    let src = r#"from snark_lib import *
def main():
    w = Array(1)
    hint_witness("w", w)
    val = w[0]
    assert val < 1000
    assert val <= 2000
    return
"#;
    assert_faithful(
        "range_checks_distinct_bounds",
        src,
        &[500],
        &[("fails val < 1000", vec![1000]), ("fails val <= 2000", vec![2001])],
    );
}

// --- 13. hint_div_floor: the quotient comparison + the always-true correctness asserts. ---
#[test]
fn hint_div_floor_then_constrain() {
    let src = r#"from snark_lib import *
def main():
    w = Array(2)
    hint_witness("w", w)
    a = w[0]
    q: Imm
    r: Imm
    hint_div_floor(a, 7, q, r)
    assert r < 7
    assert q * 7 + r == a
    assert q == w[1]
    return
"#;
    // a=100 ⇒ q=14, r=2.
    assert_faithful(
        "hint_div_floor_then_constrain",
        src,
        &[100, 14],
        &[("break q", vec![100, 15])],
    );
}

// --- 14. Two one-time memory reads asserted equal (the exact `fuse_raw_asserts` shape). ---
#[test]
fn two_reads_equal() {
    let src = r#"from snark_lib import *
def main():
    w = Array(2)
    hint_witness("w", w)
    v = w[0]
    u = w[1]
    assert v == u
    return
"#;
    assert_faithful("two_reads_equal", src, &[9, 9], &[("v != u", vec![9, 10])]);
}

// --- 15. Nested `range` loops with a runtime-indexed deref accumulator. ---
#[test]
fn nested_range_loops_grid_sum() {
    let src = r#"from snark_lib import *
def main():
    w = Array(10)
    hint_witness("w", w)
    acc = Array(10)
    acc[0] = 0
    for i in range(0, 3):
        for j in range(0, 3):
            idx = i * 3 + j
            acc[idx + 1] = acc[idx] + w[i * 3 + j]
    assert acc[9] == w[9]
    return
"#;
    // sum of 1..9 = 45.
    assert_faithful(
        "nested_range_loops_grid_sum",
        src,
        &[1, 2, 3, 4, 5, 6, 7, 8, 9, 45],
        &[("break sum", vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 46])],
    );
}

// --- 16. parallel_range with an independent per-iteration equality. ---
#[test]
fn parallel_range_per_iteration() {
    let src = r#"from snark_lib import *
def main():
    w = Array(8)
    hint_witness("w", w)
    for i in parallel_range(0, 4):
        assert w[i] == w[4 + i]
    return
"#;
    assert_faithful(
        "parallel_range_per_iteration",
        src,
        &[1, 2, 3, 4, 1, 2, 3, 4],
        &[
            ("break pair 1", vec![1, 2, 3, 4, 1, 9, 3, 4]),
            ("break pair 3", vec![1, 2, 3, 4, 1, 2, 3, 9]),
        ],
    );
}

// --- 17. match_range result feeding a loop accumulator (match + loop + constraint). ---
#[test]
fn match_then_loop_accumulator() {
    let src = r#"from snark_lib import *
def sq(n: Const):
    return n * n
def main():
    w = Array(2)
    hint_witness("w", w)
    sel = w[0]
    base = match_range(sel, range(1, 5), lambda i: sq(i))
    acc = Array(4)
    acc[0] = base
    for i in range(0, 3):
        acc[i + 1] = acc[i] + base
    assert acc[3] == w[1]
    return
"#;
    // sel=3 ⇒ base=9; acc = 9 + 3*9 = 36.
    assert_faithful(
        "match_then_loop_accumulator",
        src,
        &[3, 36],
        &[("break exp", vec![3, 37])],
    );
}

// --- 18. Algebraic-simplification trap: `a - a` folds to 0 but the residual w[1] == w[2] survives. ---
#[test]
fn algebraic_simplification_residual() {
    let src = r#"from snark_lib import *
def main():
    w = Array(3)
    hint_witness("w", w)
    a = w[0]
    z = a - a
    t = z + w[1]
    assert t == w[2]
    return
"#;
    assert_faithful(
        "algebraic_simplification_residual",
        src,
        &[7, 5, 5],
        &[("break w[1] == w[2]", vec![7, 5, 6])],
    );
}

// === Soundness-condition probes: the trickiest CSE / fusion preconditions. ===

// --- 19. CSE must NOT merge `a - b` with `b - a` (Sub is non-commutative). If it wrongly did, the
//         honest run itself fails (it would force a-b == b-a). ---
#[test]
fn cse_non_commutative_sub() {
    let src = r#"from snark_lib import *
def main():
    w = Array(4)
    hint_witness("w", w)
    a = w[0]
    b = w[1]
    d1 = a - b
    d2 = b - a
    assert d1 == w[2]
    assert d2 == w[3]
    return
"#;
    let bma = sub_mod(3, 10); // b - a = -7 mod p
    assert_faithful(
        "cse_non_commutative_sub",
        src,
        &[10, 3, 7, bma],
        &[
            ("break a-b", vec![10, 3, 8, bma]),
            ("break b-a", vec![10, 3, 7, add_mod(bma, 1)]),
        ],
    );
}

// --- 20. CSE must NOT merge `a / b` with `b / a` (Div is non-commutative). ---
#[test]
fn cse_non_commutative_div() {
    let src = r#"from snark_lib import *
def main():
    w = Array(4)
    hint_witness("w", w)
    a = w[0]
    b = w[1]
    q1 = a / b
    q2 = b / a
    assert q1 == w[2]
    assert q2 == w[3]
    return
"#;
    let aob = div_canonical(12, 3); // = 4
    let boa = div_canonical(3, 12); // = 3 * 12^{-1} mod p
    assert_faithful(
        "cse_non_commutative_div",
        src,
        &[12, 3, aob, boa],
        &[
            ("break a/b", vec![12, 3, add_mod(aob, 1), boa]),
            ("break b/a", vec![12, 3, aob, add_mod(boa, 1)]),
        ],
    );
}

// --- 21. A value used twice (assert + later arithmetic) must NOT be fused away; both checks hold. ---
#[test]
fn multi_use_no_fusion() {
    let src = r#"from snark_lib import *
def main():
    w = Array(4)
    hint_witness("w", w)
    v = w[0]
    assert v == w[1]
    u = v + w[2]
    assert u == w[3]
    return
"#;
    // v=7, ev=7, d=5, u=12.
    assert_faithful(
        "multi_use_no_fusion",
        src,
        &[7, 7, 5, 12],
        &[("break v==ev", vec![7, 8, 5, 12]), ("break u==eu", vec![7, 7, 5, 13])],
    );
}

// --- 22. Chained contiguous `match_range` (two ranges stitched). ---
#[test]
fn match_range_chained() {
    let src = r#"from snark_lib import *
def f0(i: Const):
    return i + 100
def f1(i: Const):
    return i + 200
def main():
    w = Array(2)
    hint_witness("w", w)
    sel = w[0]
    r = match_range(sel, range(0, 2), lambda i: f0(i), range(2, 5), lambda i: f1(i))
    assert r == w[1]
    return
"#;
    // sel=3 ⇒ second range ⇒ f1(3) = 203.
    assert_faithful("match_range_chained", src, &[3, 203], &[("break exp", vec![3, 204])]);
}

// --- 23. A CSE'd subexpression reused inside a taken branch; both its asserts must hold. ---
#[test]
fn cse_value_used_across_branch() {
    let src = r#"from snark_lib import *
def main():
    w = Array(4)
    hint_witness("w", w)
    x = w[0]
    t = x * x
    assert t == w[1]
    if w[2] == 1:
        u = t + x
        assert u == w[3]
    return
"#;
    // x=4 ⇒ t=16; take branch (w[2]=1) ⇒ u = 16+4 = 20.
    assert_faithful(
        "cse_value_used_across_branch",
        src,
        &[4, 16, 1, 20],
        &[("break t", vec![4, 17, 1, 20]), ("break u", vec![4, 16, 1, 21])],
    );
}

// === Kitchen-sink: maximally nested programs mixing everything at once. ===

// --- 24. Nested `range` loops + `@inline` + per-row checkpoints + a grand total. ---
#[test]
fn mega_nested_loops_inline_rowsum() {
    let src = r#"from snark_lib import *
@inline
def f(v):
    return v * v + 1
def main():
    w = Array(13)
    hint_witness("w", w)
    total = Array(4)
    total[0] = 0
    row = Array(12)
    for i in range(0, 3):
        row[i * 4] = 0
        for j in range(0, 3):
            row[i * 4 + j + 1] = row[i * 4 + j] + f(w[i * 3 + j])
        assert row[i * 4 + 3] == w[9 + i]
        total[i + 1] = total[i] + row[i * 4 + 3]
    assert total[3] == w[12]
    return
"#;
    // grid 1..9, f(v)=v*v+1 ⇒ rows 17,80,197 ; total 294.
    assert_faithful(
        "mega_nested_loops_inline_rowsum",
        src,
        &[1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 80, 197, 294],
        &[
            ("break row 1", vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 81, 197, 294]),
            ("break total", vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 80, 197, 295]),
        ],
    );
}

// --- 25. `match_range` dispatch inside a `range` loop feeding a running product with checkpoints. ---
#[test]
fn mega_match_in_loop_running_product() {
    let src = r#"from snark_lib import *
def cube(n: Const):
    return n * n * n
def main():
    w = Array(8)
    hint_witness("w", w)
    acc = Array(5)
    acc[0] = 1
    for i in range(0, 4):
        s = w[i]
        c = match_range(s, range(0, 4), lambda k: cube(k))
        acc[i + 1] = acc[i] * c
        assert acc[i + 1] == w[4 + i]
    return
"#;
    // sels 1,2,3,2 ⇒ cubes 1,8,27,8 ⇒ acc 1,8,216,1728.
    assert_faithful(
        "mega_match_in_loop_running_product",
        src,
        &[1, 2, 3, 2, 1, 8, 216, 1728],
        &[
            ("break product@2", vec![1, 2, 3, 2, 1, 8, 217, 1728]),
            ("break product@3", vec![1, 2, 3, 2, 1, 8, 216, 1729]),
        ],
    );
}

// --- 26. Bit decomposition + reconstruction + range check + conditional sum-of-positions. ---
#[test]
fn mega_bitdecomp_range_conditional() {
    let src = r#"from snark_lib import *
def main():
    w = Array(10)
    hint_witness("w", w)
    acc: Mut = 0
    for i in unroll(0, 8):
        bit = w[i]
        assert bit * (bit - 1) == 0
        acc = acc * 2 + bit
    assert acc == w[8]
    assert acc < 200
    bitsum: Mut = 0
    for i in unroll(0, 8):
        if w[i] == 1:
            bitsum = bitsum + (i + 1)
    assert bitsum == w[9]
    return
"#;
    // bits 0,0,0,0,1,1,0,1 ⇒ value 13 (<200); set positions i=4,5,7 ⇒ sum (5+6+8)=19.
    assert_faithful(
        "mega_bitdecomp_range_conditional",
        src,
        &[0, 0, 0, 0, 1, 1, 0, 1, 13, 19],
        &[
            ("non-boolean bit", vec![0, 0, 0, 0, 2, 1, 0, 1, 13, 19]),
            ("wrong reconstruction", vec![0, 0, 0, 0, 1, 1, 0, 1, 14, 19]),
            ("wrong position sum", vec![0, 0, 0, 0, 1, 1, 0, 1, 13, 20]),
            // all-ones ⇒ value 255 ≥ 200 ⇒ range check fires (reconstruction+booleans pass).
            ("value out of range", vec![1, 1, 1, 1, 1, 1, 1, 1, 255, 36]),
        ],
    );
}

// --- 27. The works: a `range` loop with `if`/`else` + `@inline` accumulation and per-iteration
//         checkpoints, followed by an extension-field dot-product checked coordinate-by-coordinate. ---
#[test]
fn mega_kitchen_sink() {
    let a = [1u64, 2, 3, 4, 5];
    let b = [6u64, 7, 8, 9, 10];
    let ext = ext_op_eval(ExtOp::Dot, ExtMode::Ee, &a, &b, 1);
    // x = [1,0,2,3,0]; acc: +w2(1)=2, +1=3, +w2(2)=7, +w2(3)=13, +1=14 ⇒ checkpoints 2,3,7,13,14.
    let mut honest: Vec<u64> = vec![1, 0, 2, 3, 0, 2, 3, 7, 13, 14];
    honest.extend(a);
    honest.extend(b);
    honest.extend(ext);
    assert_eq!(honest.len(), 25);

    let mut break_chk = honest.clone();
    break_chk[7] += 1; // perturb a per-iteration checkpoint
    let mut break_ext = honest.clone();
    break_ext[22] += 1; // perturb an extension-field result coordinate

    let src = r#"from snark_lib import *
@inline
def w2(v):
    return v * 2
def main():
    w = Array(25)
    hint_witness("w", w)
    acc = Array(6)
    acc[0] = 0
    for i in range(0, 5):
        x = w[i]
        delta: Imm
        if x == 0:
            delta = 1
        else:
            delta = w2(x)
        acc[i + 1] = acc[i] + delta
        assert acc[i + 1] == w[5 + i]
    res = Array(5)
    dot_product_ee(w + 10, w + 15, res)
    for i in unroll(0, 5):
        assert res[i] == w[20 + i]
    return
"#;
    assert_faithful(
        "mega_kitchen_sink",
        src,
        &honest,
        &[("break checkpoint", break_chk), ("break ext coord", break_ext)],
    );
}

// --- 28. Base-4 chunk decomposition: per-chunk range check + reconstruction. ---
#[test]
fn mega_chunk_range_decomposition() {
    let src = r#"from snark_lib import *
def main():
    w = Array(5)
    hint_witness("w", w)
    acc: Mut = 0
    for i in unroll(0, 4):
        chunk = w[i]
        assert chunk < 4
        acc = acc * 4 + chunk
    assert acc == w[4]
    return
"#;
    // chunks 3,1,2,0 ⇒ acc = ((3*4+1)*4+2)*4+0 = 216.
    assert_faithful(
        "mega_chunk_range_decomposition",
        src,
        &[3, 1, 2, 0, 216],
        &[
            ("chunk out of range", vec![4, 1, 2, 0, 216]),
            ("wrong reconstruction", vec![3, 1, 2, 0, 217]),
        ],
    );
}

// --- 29. range loop carrying a mutable accumulator, body is a 2-deep nested if/else over a
//         forward-declared `: Imm` assigned in all four leaves. ---
#[test]
fn mega_deep_nested_if_in_loop() {
    let src = r#"from snark_lib import *
def main():
    w = Array(6)
    hint_witness("w", w)
    acc = Array(3)
    acc[0] = 0
    for i in range(0, 2):
        a = w[2 * i]
        b = w[2 * i + 1]
        r: Imm
        if a == 0:
            if b == 0:
                r = 1
            else:
                r = 2
        else:
            if b == 0:
                r = 3
            else:
                r = 4
        acc[i + 1] = acc[i] + r
        assert acc[i + 1] == w[4 + i]
    return
"#;
    // i0: a=0,b=1 ⇒ r=2 ⇒ acc=2 ; i1: a=1,b=1 ⇒ r=4 ⇒ acc=6.
    assert_faithful(
        "mega_deep_nested_if_in_loop",
        src,
        &[0, 1, 1, 1, 2, 6],
        &[
            ("break chk0", vec![0, 1, 1, 1, 3, 6]),
            ("break chk1", vec![0, 1, 1, 1, 2, 7]),
        ],
    );
}

// --- 30. `match_range` inside an `if` inside a `range` loop, result declared in the loop scope
//         and read after the branch. Regression for the outer-scope-target shadowing miscompile
//         (fixed in main bdbce03; see crates/lean_compiler/tests/test_data/program_183.py): the
//         `match_range` expansion used to forward-declare its target at a second, shadowing cell,
//         so the arms wrote one cell while the read after the branch hit the (uninitialized) outer
//         one. Honest path exercises both the match_range arm (i=0) and the else arm (i=1). ---
#[test]
fn mega_match_range_in_if_in_loop() {
    let src = r#"from snark_lib import *
def sq(n: Const):
    return n * n
def main():
    w = Array(6)
    hint_witness("w", w)
    acc = Array(3)
    acc[0] = 0
    for i in range(0, 2):
        contrib: Imm
        if w[i] != 0:
            contrib = match_range(w[2 + i], range(0, 4), lambda k: sq(k))
        else:
            contrib = 100
        acc[i + 1] = acc[i] + contrib
        assert acc[i + 1] == w[4 + i]
    return
"#;
    // i0: w[0]=1≠0 ⇒ contrib=sq(w[2]=2)=4 ⇒ acc=4=w[4].
    // i1: w[1]=0    ⇒ contrib=100        ⇒ acc=104=w[5].
    assert_faithful(
        "mega_match_range_in_if_in_loop",
        src,
        &[1, 0, 2, 0, 4, 104],
        &[
            ("break chk0", vec![1, 0, 2, 0, 5, 104]),
            ("break chk1", vec![1, 0, 2, 0, 4, 105]),
        ],
    );
}
