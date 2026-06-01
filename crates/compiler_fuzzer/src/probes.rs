//! Curated, hand-written edge-case programs that target the compiler's panic surface.
//!
//! Unlike the structured generator (which emits *valid* programs and tests check enforcement),
//! these probes deliberately poke at parser/simplifier corners that the understanding pass
//! flagged as `panic!`/`unwrap()`/`unreachable!()`/overflow risks. Each must either compile or be
//! rejected with a clean `CompileError` — **never** unwind. A probe that panics is a compiler
//! bug (goal #1).

use std::path::Path;
use std::time::Duration;

use crate::subprocess::{SubprocessOutcome, compile_in_subprocess};
use crate::triage::{Finding, FindingKind};

/// A named probe program.
#[derive(Debug, Clone, Copy)]
pub struct Probe {
    pub name: &'static str,
    /// What corner it targets.
    pub targets: &'static str,
    pub source: &'static str,
}

/// The probe corpus. Grows as new panic-prone corners are discovered.
pub const PROBES: &[Probe] = &[
    Probe {
        name: "len_of_scalar_const",
        targets: "ConstArrayValue::len() on a scalar (parsers/mod.rs panic)",
        source: "from snark_lib import *\nS = 42\ndef main():\n    x = len(S)\n    assert x == 1\n    return\n",
    },
    Probe {
        name: "len_of_scalar_array_elem",
        targets: "len() of an indexed scalar element",
        source: "from snark_lib import *\nA = [1, 2, 3]\ndef main():\n    x = len(A[0])\n    assert x == 1\n    return\n",
    },
    Probe {
        name: "huge_unroll_bound",
        targets: "unroll bound to_usize() on a huge constant",
        source: "from snark_lib import *\ndef main():\n    for i in unroll(0, 100000000000):\n        x = i\n    return\n",
    },
    Probe {
        name: "huge_exp",
        targets: "Exp constant folding with a huge exponent",
        source: "from snark_lib import *\nX = 2 ** 9999999999\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "log2_ceil_zero",
        targets: "log2_ceil(0) compile-time eval",
        source: "from snark_lib import *\nX = log2_ceil(0)\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "div_floor_by_zero_const",
        targets: "div_floor(_, 0) compile-time eval",
        source: "from snark_lib import *\nX = div_floor(5, 0)\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "mod_by_zero_const",
        targets: "% by zero at compile time",
        source: "from snark_lib import *\nX = 5 % 0\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "overflowing_literal",
        targets: "integer literal far beyond the field modulus / u32",
        source: "from snark_lib import *\ndef main():\n    x = 99999999999999999999999999\n    return\n",
    },
    Probe {
        name: "literal_just_below_2_64",
        targets: "literal near u64::MAX",
        source: "from snark_lib import *\ndef main():\n    x = 18446744073709551615\n    return\n",
    },
    Probe {
        name: "match_out_of_range_runtime",
        targets: "match dispatch on an out-of-range value (UB, must not panic compiler)",
        source: "from snark_lib import *\ndef main():\n    p = 0\n    v = p[0]\n    match v:\n        case 0:\n            x = 1\n        case 1:\n            x = 2\n    return\n",
    },
    Probe {
        name: "empty_match_range",
        targets: "match_range with an empty/degenerate range",
        source: "from snark_lib import *\ndef main():\n    p = 0\n    r = match_range(p[0], range(0, 0), lambda i: i)\n    return\n",
    },
    Probe {
        name: "negative_array_size_expr",
        targets: "Array() with a constant that underflows",
        source: "from snark_lib import *\ndef main():\n    a = Array(saturating_sub(2, 5))\n    return\n",
    },
    Probe {
        name: "deeply_nested_expr",
        targets: "very deep expression nesting (recursion depth in parser/simplifier)",
        // Built at const-eval time: a chain of additions.
        source: "from snark_lib import *\ndef main():\n    x = ((((((((((1+1)+1)+1)+1)+1)+1)+1)+1)+1)+1)\n    assert x == 11\n    return\n",
    },
    Probe {
        name: "self_recursive_no_base",
        targets: "compile of unbounded self-recursion (should compile; runs forever only at exec)",
        source: "from snark_lib import *\ndef main():\n    x = f(0)\n    return\ndef f(n):\n    return f(n + 1)\n",
    },
    Probe {
        name: "return_arity_mismatch",
        targets: "inconsistent return arities (must be a clean error)",
        source: "from snark_lib import *\ndef main():\n    a, b = f(0)\n    return\ndef f(n):\n    if n == 0:\n        return 1\n    else:\n        return 1, 2\n",
    },
    Probe {
        name: "assert_false_only",
        targets: "assert False as the sole statement (Panic lowering)",
        source: "from snark_lib import *\ndef main():\n    assert False\n",
    },
    Probe {
        name: "unroll_reversed_bounds",
        targets: "unroll(5, 0) — start > end",
        source: "from snark_lib import *\ndef main():\n    for i in unroll(5, 0):\n        x = i\n    return\n",
    },
    Probe {
        name: "const_index_out_of_bounds",
        targets: "compile-time array index past the end",
        source: "from snark_lib import *\nA = [1, 2, 3]\ndef main():\n    x = A[10]\n    return\n",
    },
    Probe {
        name: "div_ceil_by_zero_const",
        targets: "div_ceil(_, 0) compile-time eval (divisor_nonzero -> None)",
        source: "from snark_lib import *\nX = div_ceil(5, 0)\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "next_multiple_of_zero_const",
        targets: "next_multiple_of(_, 0) compile-time eval (mod/div by zero)",
        source: "from snark_lib import *\nX = next_multiple_of(5, 0)\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "nested_const_array_col_oob",
        targets: "compile-time nested-array column index past the end",
        source: "from snark_lib import *\nA = [[1, 2], [3]]\ndef main():\n    x = A[0][5]\n    return\n",
    },
    Probe {
        name: "nested_const_array_row_oob",
        targets: "compile-time nested-array row index past the end",
        source: "from snark_lib import *\nA = [[1, 2], [3]]\ndef main():\n    x = A[5][0]\n    return\n",
    },
    Probe {
        name: "compound_assign_immutable",
        targets: "+= on an immutable binding (must be a clean error, not a panic)",
        source: "from snark_lib import *\ndef main():\n    x = 5\n    x += 1\n    return\n",
    },
    Probe {
        name: "array_size_zero",
        targets: "Array(0) zero-length allocation",
        source: "from snark_lib import *\ndef main():\n    a = Array(0)\n    return\n",
    },
    Probe {
        name: "match_range_noncontiguous",
        targets: "match_range with a gap between ranges (must be a clean error)",
        source: "from snark_lib import *\ndef sq(n):\n    return n * n\ndef main():\n    p = 0\n    r = match_range(p[0], range(0, 2), lambda i: sq(i), range(3, 5), lambda i: sq(i))\n    return\n",
    },
    Probe {
        name: "assert_gt_operator",
        targets: "`>` operator (not in grammar) must reject cleanly, not panic",
        source: "from snark_lib import *\ndef main():\n    p = 0\n    assert p[0] > 5\n    return\n",
    },
    Probe {
        name: "self_referential_const",
        targets: "X = X self-referential constant",
        source: "from snark_lib import *\nX = X\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "duplicate_const_name",
        targets: "two top-level constants with the same name",
        source: "from snark_lib import *\nX = 1\nX = 2\ndef main():\n    y = X\n    return\n",
    },
    Probe {
        name: "main_without_return",
        targets: "function with no return statement (must be a clean error)",
        source: "from snark_lib import *\ndef main():\n    x = 1\n",
    },
    Probe {
        name: "len_of_runtime_value",
        targets: "len() of a runtime (non-const) value",
        source: "from snark_lib import *\ndef main():\n    p = 0\n    x = len(p[0])\n    return\n",
    },
    Probe {
        name: "unroll_huge_via_const_exp",
        targets: "unroll bound from a const-folded 2**40 (MAX_UNROLL_ITERATIONS cap)",
        source: "from snark_lib import *\nN = 2 ** 40\ndef main():\n    for i in unroll(0, N):\n        x = i\n    return\n",
    },
    Probe {
        name: "huge_const_array_alloc",
        targets: "Array() with a near-2^31 compile-time size (must not OOM/abort the compiler)",
        source: "from snark_lib import *\ndef main():\n    a = Array(2000000000)\n    return\n",
    },
    Probe {
        name: "match_range_zero_arms_lambda",
        targets: "match_range single empty range",
        source: "from snark_lib import *\ndef main():\n    p = 0\n    r = match_range(p[0], range(2, 2), lambda i: i)\n    return\n",
    },
    Probe {
        name: "div_by_self_minus_self",
        targets: "runtime division by a computed value (UB at runtime; must compile)",
        source: "from snark_lib import *\ndef main():\n    p = 0\n    a = p[0]\n    b = a - a\n    c = a / b\n    return\n",
    },
];

/// Default per-probe wall-clock timeout.
pub const PROBE_TIMEOUT: Duration = Duration::from_secs(10);
/// Default per-probe address-space limit (2 GiB) — bounds an OOM blowup to the child.
pub const PROBE_MEM_LIMIT: u64 = 2 << 30;

/// Run every probe (static + dynamic stressors) in a bounded subprocess. Returns a finding for
/// each probe that does anything other than cleanly compile or cleanly reject (panic / hang /
/// crash). `bin` is the path to this crate's binary.
#[must_use]
pub fn run_probes(bin: &Path) -> Vec<Finding> {
    let mut findings = Vec::new();
    let mut seed = 0u64;
    for p in PROBES {
        run_probe(bin, seed, p.name, p.targets, p.source, &mut findings);
        seed += 1;
    }
    for (name, targets, source) in dynamic_stressors() {
        run_probe(bin, seed, &name, &targets, &source, &mut findings);
        seed += 1;
    }
    findings
}

/// Compile one probe source in a bounded subprocess and push a finding if it did not cleanly
/// compile/reject.
fn run_probe(bin: &Path, seed: u64, name: &str, targets: &str, source: &str, findings: &mut Vec<Finding>) {
    let outcome = match compile_in_subprocess(bin, source, PROBE_TIMEOUT, PROBE_MEM_LIMIT) {
        Ok(o) => o,
        Err(e) => {
            findings.push(Finding::new(
                FindingKind::CompilerCrash,
                seed,
                format!("probe `{name}` ({targets}): failed to spawn compiler subprocess: {e}"),
                source,
            ));
            return;
        }
    };
    if let Some(f) = classify_outcome(seed, name, targets, source, &outcome) {
        findings.push(f);
    }
}

/// Map a non-clean subprocess outcome to a finding.
fn classify_outcome(
    seed: u64,
    name: &str,
    targets: &str,
    source: &str,
    outcome: &SubprocessOutcome,
) -> Option<Finding> {
    let (kind, detail) = match outcome {
        SubprocessOutcome::Compiled | SubprocessOutcome::Rejected => return None,
        SubprocessOutcome::Panicked(msg) => (FindingKind::CompilerPanic, format!("panicked: {msg}")),
        SubprocessOutcome::Timeout => (FindingKind::CompilerHang, format!("hung (> {PROBE_TIMEOUT:?})")),
        SubprocessOutcome::Crashed { signal, .. } => (FindingKind::CompilerCrash, format!("fatal signal {signal}")),
        SubprocessOutcome::UnexpectedExit { code, .. } => {
            (FindingKind::CompilerCrash, format!("unexpected exit code {code}"))
        }
    };
    Some(Finding::new(
        kind,
        seed,
        format!("probe `{name}` ({targets}): {detail}"),
        source,
    ))
}

/// Programmatically-built stressors that target *unbounded recursion / pathological size* in the
/// parser and simplifier — the kind of input no hand-written corpus reaches. Each must either
/// compile, reject cleanly, or (acceptably) hit the resource bound; a panic / fatal signal (e.g. a
/// stack overflow → SIGSEGV) is a compiler bug. Depths are chosen to plausibly exhaust a default
/// 8 MiB stack if recursion is unguarded.
#[must_use]
pub fn dynamic_stressors() -> Vec<(String, String, String)> {
    let mut out = Vec::new();

    // Deeply nested parenthesized expression: `(((…1…)))`.
    {
        let d = 6000;
        let body = format!("{}1{}", "(".repeat(d), ")".repeat(d));
        out.push((
            "deep_nested_parens".to_string(),
            format!("expression nesting depth {d} (parser/simplifier recursion)"),
            format!("from snark_lib import *\ndef main():\n    x = {body}\n    return\n"),
        ));
    }
    // Long left-associated constant-fold chain: `1 + 1 + … + 1`.
    {
        let n = 40_000;
        let body = vec!["1"; n].join(" + ");
        out.push((
            "long_add_chain".to_string(),
            format!("{n}-term constant-fold chain (const-eval recursion / stack)"),
            format!("from snark_lib import *\ndef main():\n    x = {body}\n    return\n"),
        ));
    }
    // Deeply nested `if` blocks (simplifier recurses per nested block).
    {
        let d = 1500;
        let mut s = String::from("from snark_lib import *\ndef main():\n    p = 0\n");
        for i in 0..d {
            s.push_str(&"    ".repeat(i + 1));
            s.push_str("if p[0] == 0:\n");
        }
        s.push_str(&"    ".repeat(d + 1));
        s.push_str("x = 1\n    return\n");
        out.push((
            "deep_nested_if".to_string(),
            format!("{d} nested if-blocks (simplifier block recursion)"),
            s,
        ));
    }
    // Deeply nested constant-array literal: `[[[…1…]]]`.
    {
        let d = 3000;
        let lit = format!("{}1{}", "[".repeat(d), "]".repeat(d));
        out.push((
            "deep_nested_array_literal".to_string(),
            format!("array-literal nesting depth {d} (parser recursion)"),
            format!("from snark_lib import *\nA = {lit}\ndef main():\n    y = 0\n    return\n"),
        ));
    }
    // Long chain of (non-inline) function calls f0 -> f1 -> … -> fN.
    {
        let n = 3000;
        let mut s = String::from("from snark_lib import *\ndef main():\n    x = f0(0)\n    return\n");
        for i in 0..n {
            s.push_str(&format!("def f{i}(v):\n    return f{}(v + 1)\n", i + 1));
        }
        s.push_str(&format!("def f{n}(v):\n    return v\n"));
        out.push((
            "deep_call_chain".to_string(),
            format!("{n}-deep function-call chain (call resolution / inlining recursion)"),
            s,
        ));
    }
    // Very wide straight-line program (many sequential statements).
    {
        let n = 40_000;
        let mut s = String::from("from snark_lib import *\ndef main():\n    a0 = 0\n");
        for i in 1..n {
            s.push_str(&format!("    a{i} = a{} + 1\n", i - 1));
        }
        s.push_str("    return\n");
        out.push((
            "very_wide_program".to_string(),
            format!("{n} sequential statements (linear scaling / memory)"),
            s,
        ));
    }

    out
}
