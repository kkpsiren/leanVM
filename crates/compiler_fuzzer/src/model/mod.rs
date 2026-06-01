//! The fuzzer's program model: an abstract description of a generated zkDSL program that
//! doubles as a reference interpreter.
//!
//! A [`CheckedProgram`] is an ordered list of independent [`Gadget`]s. Each gadget reads a
//! private hint buffer, performs a [`Computation`], and ends in exactly one target check. The
//! model can emit the program as zkDSL *and* compute, by construction, the honest witness
//! (every check passes) and, per gadget, a witness that makes only that gadget's check fail.
//! That construction-by-knowledge is what gives the check-enforcement oracle its isolation.

pub mod comp;
pub mod emit;
pub mod gadget;
pub mod program;

pub use comp::{Computation, Op, Operand, Step};
pub use emit::Emitter;
pub use gadget::{Gadget, GadgetKind, RANGE_MAX};
pub use program::{CheckedProgram, HINT_LABEL};
