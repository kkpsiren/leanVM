//! Tests for the two-stage compilation pipeline:
//! zkDSL -> intermediate zkDSL (printed as .py source) -> bytecode.

use backend::PrimeCharacteristicRing;
use lean_compiler::*;
use lean_vm::*;

fn run(program: &str) {
    let bytecode = try_compile_program(&ProgramSource::Raw(program.to_string())).unwrap();
    try_execute_bytecode(
        &bytecode,
        &[F::ZERO; PUBLIC_INPUT_LEN],
        &ExecutionWitness::default(),
        false,
    )
    .unwrap();
}

const SUGAR_HEAVY_PROGRAM: &str = r#"
N = 3

@inline
def square(x):
    return x * x

def scaled(x, factor: Const):
    return x * factor

def main():
    total: Mut = 0
    for i in unroll(0, N):
        total = total + square(i)
    assert total == 5
    acc = Array(5)
    acc[0] = total
    for i in range(0, 4):
        v = match_range(i, range(0, 4), lambda k: scaled(acc[i], k))
        acc[i + 1] = v + 1
    x: Mut = acc[4]
    if x == 16:
        x = 100
    else:
        x = x + 1
        assert x != 0
    assert x == 100
    return
"#;

/// The intermediate program drops every eliminated construct and is accepted
/// by the second stage.
#[test]
fn test_intermediate_subset() {
    let intermediate = try_compile_to_intermediate_source(
        &ProgramSource::Raw(SUGAR_HEAVY_PROGRAM.to_string()),
        CompilationFlags::default(),
    )
    .unwrap();

    assert!(!intermediate.contains(": Mut"), "{intermediate}");
    assert!(!intermediate.contains("unroll"), "{intermediate}");
    assert!(!intermediate.contains("match_range"), "{intermediate}");
    assert!(!intermediate.contains("lambda"), "{intermediate}");
    assert!(!intermediate.contains("@"), "{intermediate}");
    // `range` loops and `match` survive.
    assert!(intermediate.contains("in range("), "{intermediate}");
    assert!(intermediate.contains("match "), "{intermediate}");

    let bytecode = try_compile_intermediate_source(&intermediate).unwrap();
    try_execute_bytecode(
        &bytecode,
        &[F::ZERO; PUBLIC_INPUT_LEN],
        &ExecutionWitness::default(),
        false,
    )
    .unwrap();
}

/// The second stage rejects programs outside the intermediate subset.
#[test]
fn test_intermediate_rejects_sugar() {
    let mutable_var = "def main():\n    x: Mut = 0\n    x = 1\n    return\n";
    assert!(try_compile_intermediate_source(mutable_var).is_err());

    let unrolled = "def main():\n    a = Array(2)\n    for i in unroll(0, 2):\n        a[i] = i\n    return\n";
    assert!(try_compile_intermediate_source(unrolled).is_err());

    let inlined = "@inline\ndef f(x):\n    return x\n\ndef main():\n    y = f(1)\n    return\n";
    assert!(try_compile_intermediate_source(inlined).is_err());

    let const_arg = "def f(x: Const):\n    return x\n\ndef main():\n    y = f(1)\n    return\n";
    assert!(try_compile_intermediate_source(const_arg).is_err());
}

/// `__` identifiers are reserved in user programs, but legal in intermediate ones.
#[test]
fn test_reserved_identifiers() {
    let reserved = "def main():\n    __x = 1\n    assert __x == 1\n    return\n";
    assert!(try_compile_program(&ProgramSource::Raw(reserved.to_string())).is_err());
    assert!(try_compile_intermediate_source(reserved).is_ok());
}

/// A function without any `return` is allowed when it always panics.
#[test]
fn test_function_without_return() {
    run(r#"
def fail():
    assert False, "unreachable"

def main():
    buf = Array(1)
    buf[0] = 1
    if buf[0] == 2:
        fail()
    return
"#);
}
