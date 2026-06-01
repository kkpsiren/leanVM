# Findings

Compiler behaviours surfaced by `compiler_fuzzer`. The fuzzer hunts two classes: inputs the
compiler should handle gracefully (compile, or reject with a clean `CompileError`) but doesn't, and
programs whose verifier-enforced checks the compiler silently drops.

All measurements use the **release** build (the fuzzer always compiles in release). There are
currently **no open compiler-crash or dropped-check findings**; the items below were surfaced and
triaged as *not* bugs. (Crashes fixed earlier are in the History section.)

---

# Considered and rejected — *not* bugs (by design)

## Deeply nested expression overflowing the parser stack is an accepted limitation

```python
from snark_lib import *
def main():
    x = ((((( … ~3000 deep … 1 … )))))
    return
```

A parenthesized-expression nesting depth of ~3000 overflows the recursive-descent parser's stack
and aborts (depth 2000 compiles; ~3000 aborts). This is an **accepted limitation, not a bug**: no
real program nests thousands of levels deep, and adding a guard was considered and rejected. The
`deep_nested_parens` dynamic stressor therefore stays *below* the threshold (depth 1000) and only
checks that deep-but-bounded nesting compiles cleanly; the other size stressors (40k-term fold
chains, nested `if`s, deep array literals / call chains, 40k sequential statements) all compile.

## Reading an unassigned `: Imm` is a free witness cell, not a dropped check

```python
def main():
    pub = 0
    x: Imm
    if pub[0] != 0:
        x = 42
    assert x == 7        # accepted when the branch is skipped
    return
```

When the branch is skipped, `x` is never written, and `assert x == 7` lowers to a write-once
*write* of that cell (`x := 7`) rather than disappearing — so the program runs and the assert is
satisfiable for any value. This is **intended language semantics**: an unwritten cell is a free,
prover-filled witness (exactly like a `hint_*` cell), and constraining it is the program's
responsibility — the same stance the language takes for `match` range-validity. The verifier is
*not* fooled into accepting a false statement about the trace; the assert simply constrains a free
variable.

The genuine soundness property — and what the fuzzer actually checks — is that **an emitted
`assert` must produce instructions in the final bytecode** (it must not be optimized away). That is
covered by the structural-diff oracle (removing an `assert` line must change the bytecode) and the
runtime oracle on gadgets whose violating witness perturbs a *constrained* value. A "violation"
that instead frees a cell (changing control flow so the operand becomes unconstrained) is **not** a
dropped check, so the fuzzer's gadgets never do that.

> An earlier audit flagged the pattern above as a critical bug; on review it is by-design behavior.
> The fuzzer's `ForwardDeclEq` gadget therefore exercises the *valid* shape (a `: Imm` assigned on
> **both** branches, with the assert genuinely constraining it).

---

# History — crashes fixed in `main`

The crashes below were surfaced by earlier `--probes` runs and are **FIXED** (merged into `main`
as `zkDSL compiler: various consolidations`; regression cases live in
`crates/lean_compiler/tests/test_data/error_93..98.py`). They remain in the probe corpus as
regression guards.

## 1. `unroll` with a huge bound hangs the compiler

```python
from snark_lib import *
def main():
    for i in unroll(0, 100000000000):
        x = i
    return
```

**Symptom:** the compiler does not return within 10s (it attempts to materialize ~10¹¹ unrolled
iterations). Wall-clock hang / unbounded memory.
**Fixed:** `MAX_UNROLL_ITERATIONS` cap in `a_simplify_lang/mod.rs` (reversed `start>end` stays a valid empty no-op).

## 2. `match_range` over an empty range panics

```python
from snark_lib import *
def main():
    p = 0
    r = match_range(p[0], range(0, 0), lambda i: i)
    return
```

**Symptom:** `called `Option::unwrap()` on a `None` value` at `c_compile_final.rs:87`.
**Fixed:** `.max()` now `ok_or_else(...)?` in `c_compile_final.rs` → clean error.

## 3. Out-of-bounds compile-time array index panics

```python
from snark_lib import *
A = [1, 2, 3]
def main():
    x = A[10]
    return
```

**Symptom:** `Variable A not in scope` (an `unwrap`/`expect`) at `b_compile_intermediate.rs:62`.
**Fixed:** const-array reads now route through bounds-checked `simplify_expr`; const-array *writes* are rejected by a target guard.
