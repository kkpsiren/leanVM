//! # compiler_fuzzer
//!
//! A fuzzing harness for the handcrafted `lean_compiler` zkDSL compiler.
//!
//! The compiler is handwritten across four stages (parse → simplify → intermediate →
//! final bytecode). Two properties matter above all and are the focus of this crate:
//!
//! 1. **The compiler must never panic.** Any input that the parser accepts must either
//!    compile to bytecode or be rejected with a clean `CompileError`. A panic is a bug.
//!
//! 2. **Critical runtime checks must survive compilation.** Every `assert ==`, `assert !=`,
//!    `assert <`, `assert <=`, `assert False` and `debug_assert(...)` must remain enforced
//!    in the emitted bytecode. The simplifier's fusion/propagation passes
//!    (`post_optimization.rs`) historically deleted checks; this is the prime target.
//!
//! Because the leanVM *runner* is honest (we are not proving, just executing), a check that
//! survives compilation is enforced *at runtime*: feeding a witness that violates it makes
//! `try_execute_bytecode` return an error. Conversely, if a violating witness is accepted,
//! the check was silently dropped during compilation — a critical soundness bug.
//!
//! ## Techniques
//!
//! - **Check-enforcement (differential soundness)** ([`oracles::check_enforced`]): the core
//!   technique. Generate programs built from *independent* check gadgets; run the honest
//!   witness (must pass) and, for each check, a witness that violates *only that check*
//!   (must be rejected). Failures isolate to a single check, avoiding false positives. The
//!   generator doubles as a canonical-integer reference interpreter, so witnesses pass/fail
//!   by construction.
//! - **Bytecode-structural survival** ([`oracles::structural`]): a range-check constraint can
//!   be dropped behind a surviving prover-side `debug_assert` companion (invisible to the
//!   runtime oracle). Require exactly `2 * n_range` `Hint::DerefHint`s and one companion per
//!   `<` / `<=`.
//! - **Structural-diff** ([`oracles::structural_diff`]): removing any emitted `assert` line
//!   must change the bytecode hash; needs no witness, so it covers checks no witness can
//!   violate (e.g. `hint_div_floor`'s always-true `q*D + r == a`).
//! - **No-crash probes** ([`probes`] + [`subprocess`]): panics / aborts / OOM / hangs / stack
//!   overflows, by compiling edge-case programs (and programmatic recursion/size stressors) in a
//!   bounded child process.
//! - **Metamorphic transforms** ([`transforms`]): semantics-preserving reorder / duplicate of
//!   independent gadgets must preserve pass/fail behaviour.
//!
//! Every run is driven by a 64-bit seed, so any finding reproduces exactly. See
//! [`campaign`] for the driver and [`triage`] for finding serialization.

pub mod campaign;
pub mod corpus;
pub mod field_util;
pub mod generators;
pub mod harness;
pub mod model;
pub mod oracles;
pub mod probes;
pub mod rng;
pub mod subprocess;
pub mod transforms;
pub mod triage;
