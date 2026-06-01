# Findings

Compiler bugs surfaced by `compiler_fuzzer`. Each is a *parseable* program that the compiler
must handle gracefully (compile, or reject with a clean `CompileError`) but does not. All three
are in the **crash** class (goal #1); the `--probes` mode reproduces them:

```bash
cargo run --release -p compiler_fuzzer -- --probes
```

The check-enforcement campaign (goal #2) has found **no dropped checks** across 70k+ generated
programs spanning every gadget kind and the metamorphic variants.

---

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
**Suspected site:** the unroll expansion (`a_simplify_lang/mod.rs`, the `start..end` /
`to_usize()` loop). A bound check (e.g. a cap on total unrolled iterations) would turn this into
a clean error.

## 2. `match_range` over an empty range panics

```python
from snark_lib import *
def main():
    p = 0
    r = match_range(p[0], range(0, 0), lambda i: i)
    return
```

**Symptom:** `called `Option::unwrap()` on a `None` value` at
`crates/lean_compiler/src/c_compile_final.rs:87`.
A degenerate/empty `match_range` should be a clean compile error.

## 3. Out-of-bounds compile-time array index panics

```python
from snark_lib import *
A = [1, 2, 3]
def main():
    x = A[10]
    return
```

**Symptom:** `Variable A not in scope` (an `unwrap`/`expect`) at
`crates/lean_compiler/src/b_compile_intermediate.rs:62`. A constant index past the end of a
constant array should be a clean compile error, with a message about the index, not a panic
about the variable being out of scope.

---

### Note

The understanding pass suspected `len(<scalar>)` would panic; it does **not** (it compiles), so
that probe is retained only as a regression guard. New crash corners should be added to
`probes::PROBES`.
