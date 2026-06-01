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
];

/// Default per-probe wall-clock timeout.
pub const PROBE_TIMEOUT: Duration = Duration::from_secs(10);
/// Default per-probe address-space limit (2 GiB) — bounds an OOM blowup to the child.
pub const PROBE_MEM_LIMIT: u64 = 2 << 30;

/// Run every probe in a bounded subprocess. Returns a finding for each probe that does anything
/// other than cleanly compile or cleanly reject (panic / hang / crash). `bin` is the path to
/// this crate's binary.
#[must_use]
pub fn run_probes(bin: &Path) -> Vec<Finding> {
    let mut findings = Vec::new();
    for (i, p) in PROBES.iter().enumerate() {
        let outcome = match compile_in_subprocess(bin, p.source, PROBE_TIMEOUT, PROBE_MEM_LIMIT) {
            Ok(o) => o,
            Err(e) => {
                findings.push(Finding::new(
                    FindingKind::CompilerCrash,
                    i as u64,
                    format!(
                        "probe `{}` ({}): failed to spawn compiler subprocess: {e}",
                        p.name, p.targets
                    ),
                    p.source,
                ));
                continue;
            }
        };
        if let Some(f) = finding_for(i as u64, p, &outcome) {
            findings.push(f);
        }
    }
    findings
}

/// Map a non-clean subprocess outcome to a finding.
fn finding_for(seed: u64, p: &Probe, outcome: &SubprocessOutcome) -> Option<Finding> {
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
        format!("probe `{}` ({}): {detail}", p.name, p.targets),
        p.source,
    ))
}
