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
//! - **No-panic fuzzing** ([`oracles::no_panic`]): generate / mutate programs and assert the
//!   compiler returns a `Result`, never unwinds.
//! - **Check-enforcement / metamorphic soundness** ([`oracles::check_enforced`]): the core
//!   technique. Generate programs built from *independent* check gadgets; run the honest
//!   witness (must pass) and, for each check, a witness that violates *only that check*
//!   (must be rejected with the error variant matching the check's kind). Failures isolate
//!   to a single check, avoiding false positives.
//! - **Reference-model differential** ([`oracles::honest_runs`]): the generator is also a
//!   reference interpreter; the VM's observable results must match.
//! - **Metamorphic transforms** ([`oracles::metamorphic`]): semantics-preserving rewrites
//!   (rename, reorder, inline↔call, unroll↔range, wrap) must preserve pass/fail behaviour.
//! - **Bytecode-structural survival** ([`oracles::structural`]): count the recognizable
//!   lowerings (`Hint::DerefHint`, `Hint::Panic`, `Hint::DebugAssert`, the `0 * fp == 1`
//!   panic computation) that must appear for each emitted check.
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
