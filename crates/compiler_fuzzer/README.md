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
| **Structural survival** | `oracles::structural` | A range-check constraint dropped *behind a surviving prover-side `debug_assert` companion* (which masks it at runtime). Requires exactly `2 * n_range` `Hint::DerefHint`s and one inequality companion per `<` / `<=` — fewer means a constraint was dropped even though the runtime oracle can't see it. |
| **Structural-diff** | `oracles::structural_diff` | Any emitted `assert` that compiles to *zero* instructions. Removes each `assert` line, recompiles, and flags if the bytecode hash is unchanged. Needs no witness, so it covers checks the runtime oracle can't violate (e.g. `hint_div_floor`'s `q*D + r == a`, always true for an honest runner). Run on the base program **and** the duplicate metamorphic variant (where adjacent identical gadgets stress CSE / fusion). |
| **Const-fold differential** | `model` (`ConstFold` gadget) | A miscompiled compile-time built-in (`**`, `%`, `div_floor`/`div_ceil`, `saturating_sub`, `next_multiple_of`, `log2_ceil`). The honest buffer holds an *independent* mod-`p`/integer reference; a wrong fold makes the honest witness fail. |
| **No-crash probes** | `probes` + `subprocess` | Panics, aborts, OOM, **hangs**, and **stack overflows**, by compiling edge-case programs in a bounded child process (timeout + address-space rlimit). Includes programmatic *stressors* (deep nesting, long chains, very wide programs) that no hand-written corpus reaches. |
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
    gadget.rs       ~28 gadget kinds; each emits zkDSL + builds honest/violating buffers
    program.rs      compose gadgets into main() + helpers; build ExecutionWitness
    emit.rs         indentation-aware zkDSL source builder
  generators.rs   random, seed-deterministic CheckedProgram + const-expression generation
  transforms.rs   semantics-preserving rewrites (reorder, duplicate)
  oracles/        check_enforced + structural + structural_diff; oracles::evaluate runs all
  probes.rs       curated crash-probe corpus + programmatic stressors
  triage.rs       Finding (severity, kind, seed, source, witness) + on-disk reproducers
  campaign.rs     the deterministic generate→evaluate loop
  bin/compiler_fuzz.rs  CLI soak driver + --compile-stdin child + --probes
  tests/          in-crate unit tests (no `tests/` integration dir):
    fuzzer.rs       self-tests, the negative control, the gadget isolation matrix, clean baseline
    handwritten.rs  curated faithfulness cases — tangled programs whose constraints must survive
```

## Gadget kinds

Equality/inequality family (`EqBound`, `EqConst`, `Ne`, `Bool`) plus the harder lowering paths,
which is where dropped-check bugs are most likely:

- `RangeLt` / `RangeLe` — range checks (DEREF lowering + bound soundness).
- `IfThen` / `IfElse` — an assert inside a taken `if` branch / inside an `else` branch.
- `Loop` — a `range` loop accumulator (→ recursion + mutable-buffer rewriting).
- `NestedIfLoop{n}` — an assert nested inside an `if` inside a `range` loop.
- `ParallelLoop{n}` — an assert inside a `parallel_range` body (exercises the
  `ParallelSegmentFailed` path).
- `MatchDispatch` — `match_range` dispatch to a const helper (match expansion).
- `InlineWrapped` — value routed through an `@inline` function (inlining).
- `MultiReturn` — `p, q = fz_pair(in)` (multi-value return + tuple unpacking).
- `CompoundAssign` — `x += b; x *= c` (compound-assignment lowering).
- `Div` — runtime field division `a / b`.
- `PointerOffset` — `arr[base + K]` with runtime `base`, const `K` (the
  `fold_const_offset_into_deref` pass).
- `HintDiv` — `hint_div_floor` + correctness asserts; the target compares the quotient to an
  independent input (custom-hint-then-constrain).
- `BitDecomp{n}` — `n` prover-supplied bits, each constrained boolean and reconstructed
  (`acc = acc*2 + b`), then `assert acc == expected`: the canonical hint-then-constrain
  decomposition (XMSS / range proofs). Every boolean **and** the reconstruction is an independent
  violation (`n + 1`).
- `ExtOp{op, mode, n}` — the full extension-field precompile family (`add`/`dot`/`poly_eq` in
  `ee`/`be` mode, length `n`); assert the 5-coordinate result against an independent buffer value
  (`DIMENSION` violations).
- `Panic` — `assert False` inside a taken `if` (Panic lowering behind control flow).
- `DebugAssertLt` — `debug_assert(value < bound)`; emits no bytecode, so only the runtime oracle
  can confirm it survives.
- `ConstFold` — `assert v == <const expr>` mixing `**`, `%`, `div_floor`/`div_ceil`,
  `saturating_sub`, `next_multiple_of`, `log2_ceil`. The honest buffer holds an **independent**
  mod-`p`/integer reference, so a miscompiled constant fold makes the honest witness fail — a
  differential test of the const-eval path.

Plus gadgets aimed squarely at the simplifier passes that *could* silently drop a check
(`post_optimization.rs`):

- `CopyPropEq` — `v = x + 0; assert v == exp` (copy-propagation rewrites `v = mem + 0` away; the
  assert must survive).
- `CseEq` — two identical `in0 * in1` subexpressions, each asserted against its own bound.
  Common-subexpression elimination collapses the second into the first; **both** asserts must
  remain (two independent violations).
- `TwoReadsEq` — `assert buf[0] == buf[1]`, both one-time memory reads — the exact shape
  `fuse_raw_asserts` rewrites.
- `RunningChain{len}` — a dependency chain `b_k = b_{k-1} + d_k` with an independent checkpoint
  `assert b_k == c_k` at every step (`len` independent violations); stresses repeated
  assert-fusion / copy-propagation along a chain.
- `ForwardDeclEq` — a `: Imm` forward declaration assigned on **both** branches of an `if`/`else`
  (mutually-exclusive write-once), then asserted after the merge.

A gadget can enforce several independent checks (`Gadget::n_violations()`); the oracle breaks
each one in isolation, so every link of a chain, every member of a CSE pair, and every bit of a
decomposition is tested.

> **What is *not* a dropped check.** An unassigned `: Imm` read is a free, prover-filled witness
> cell (by design — like a `hint_*` cell), so an `assert` over it is satisfiable for any value
> *but still emitted*; that is not a bug (see `FINDINGS.md`). The fuzzer's notion of a dropped
> check is "the `assert` produced no bytecode" (structural-diff) or "a violating witness that
> perturbs a *constrained* value is accepted" (runtime). Gadget violations therefore always
> perturb a constrained cell — never one made free by changing control flow.

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
`hard_kinds_isolate` and `generator_covers_hard_constructs` tests will keep you honest (every
*sound* kind must appear in `all_gadget_kinds()`). New crash corners go in `probes::PROBES`;
recursion/size stressors go in `probes::dynamic_stressors`. A gadget that reproduces a *known*
(unfixed) bug stays out of `gen_gadget` and gets a dedicated detection test instead.

See `FINDINGS.md` for bugs this harness has surfaced — including the two open ones it currently
finds.
