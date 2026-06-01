# compiler_fuzzer

A fuzzing harness for the handwritten **`lean_compiler`** zkDSL compiler (parse → simplify →
intermediate → final bytecode). It hunts two classes of bug:

1. **Compiler crashes.** Any input the parser accepts must either compile to bytecode or be
   rejected with a clean `CompileError`. A panic, abort, stack overflow, OOM, or hang is a bug.
2. **Dropped checks.** Every `assert ==`, `assert !=`, `assert <`, `assert <=`, `assert False`,
   and `debug_assert(...)` must remain *enforced* in the emitted bytecode. The simplifier's
   fusion/propagation passes (`a_simplify_lang/post_optimization.rs`) have historically deleted
   checks; that is the prime target.

Because the leanVM *runner* is honest (we execute, we don't prove), a check that survives
compilation is enforced at runtime: feed a witness that violates it and `try_execute_bytecode`
returns an error. If a violating witness is *accepted*, the check was silently dropped during
compilation — a critical soundness bug.

## Techniques

| Technique | Module | What it catches |
|-----------|--------|-----------------|
| **Check-enforcement (differential soundness)** | `oracles::check_enforced` | Dropped checks. Generate programs from *independent* gadgets; run the honest witness (must pass) and, per gadget, a witness that violates *only that gadget's* check (must be rejected). |
| **Structural survival** | `oracles::structural` | Range-check lowerings dropped *behind a surviving prover-side companion* (which masks them at runtime). Counts `Hint::DerefHint` / inequality `Hint::DebugAssert` in the bytecode. |
| **No-crash probes** | `probes` + `subprocess` | Panics, aborts, OOM, and **hangs**, by compiling edge-case programs in a bounded child process (timeout + address-space rlimit). |
| **Metamorphic transforms** | `transforms` | Order/duplication-dependent miscompiles (CSE, fusion). Reorder / duplicate independent gadgets; behaviour must not change. |
| **Reference-model differential** | `model` | Mis-evaluation: the generator is also a canonical-integer interpreter, used to build witnesses that pass/fail *by construction*. |

### Why isolation works (no false positives)

Each gadget reads its own hint buffer, uses globally-unique variable names, and writes only to
freshly-allocated memory. So composing many gadgets keeps them independent. To test gadget *i*,
the honest witness is used for every other gadget and only buffer *i* is perturbed — and because
the honest baseline passes, any resulting failure is attributable to gadget *i*. The bug verdict
is *"honest passes but the violating witness was accepted"*, which is robust regardless of which
error variant fires. (The variant is still checked for diagnostics; an inconsistent one is
reported as `Info`, never as a confirmed drop.)

## Layout

```
src/
  rng.rs          deterministic SplitMix64 — one u64 seed reproduces everything
  field_util.rs   integers <-> KoalaBear F / quintic EF; canonical-integer arithmetic
  harness/        compile (catch_unwind + panic capture) + run + RunnerError classification
  subprocess.rs   out-of-process compile with timeout + memory rlimit (catches abort/OOM/hang)
  model/          the program model = reference interpreter
    comp.rs         straight-line field computation (emit + eval)
    gadget.rs       11 gadget kinds; each emits zkDSL + builds honest/violating buffers
    program.rs      compose gadgets into main() + helpers; build ExecutionWitness
    emit.rs         indentation-aware zkDSL source builder
  generators.rs   random, seed-deterministic CheckedProgram generation
  transforms.rs   semantics-preserving rewrites (reorder, duplicate)
  oracles/        check_enforced + structural; oracles::evaluate compiles once, runs all
  probes.rs       curated crash-probe corpus
  triage.rs       Finding (severity, kind, seed, source, witness) + on-disk reproducers
  campaign.rs     the deterministic generate→evaluate loop
  bin/compiler_fuzz.rs  CLI soak driver + --compile-stdin child + --probes
tests/fuzzer.rs   self-tests incl. the negative control + a clean-baseline regression guard
```

## Gadget kinds

Equality/inequality family (`EqBound`, `EqConst`, `Ne`, `Bool`) plus the harder lowering paths,
which is where dropped-check bugs are most likely:

- `RangeLt` / `RangeLe` — range checks (DEREF lowering + bound soundness).
- `IfThen` — an assert inside a taken `if` branch.
- `Loop` — a `range` loop accumulator (→ recursion + mutable-buffer rewriting).
- `MatchDispatch` — `match_range` dispatch to a const helper (match expansion).
- `InlineWrapped` — value routed through an `@inline` function (inlining).
- `HintDiv` — `hint_div_floor` + correctness asserts; the target compares the quotient to an
  independent input (custom-hint-then-constrain).

## Running

```bash
# Soak the structured generator (deterministic; seeds [S, S+N)).
cargo run --release -p compiler_fuzzer -- --seed 0 --iters 100000 --out crates/compiler_fuzzer/findings

# Crash probes (panic/hang/abort) — each in a bounded subprocess.
cargo run --release -p compiler_fuzzer -- --probes

# Self-tests + bounded regression baseline (part of `cargo testall`).
cargo test -p compiler_fuzzer
```

Flags: `--seed S`, `--iters N`, `--out DIR`, `--quiet`, `--stop-on-critical`. Exit code is
non-zero if any Critical/High finding appears.

## Reproducing a finding

Each finding is written to `--out` as `<seed>_<kind>[_gN].py` (the exact program) plus a
`.json` (seed, kind, gadget, severity, and the witness buffers). The `.py` can be fed straight
to the compiler; the seed alone re-derives everything via `Rng::new(seed)`.

## Extending

Add a `GadgetKind` variant and implement its `emit` / `honest_buffer` / `violating_buffer`
(and `helpers` if it needs a top-level function), then add it to `gen_gadget`. The
`hard_kinds_isolate` and `generator_covers_hard_constructs` tests will keep you honest. New
crash corners go in `probes::PROBES`.

See `FINDINGS.md` for bugs this harness has already surfaced.
