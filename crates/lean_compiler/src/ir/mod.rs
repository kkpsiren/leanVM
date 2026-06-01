//! Intermediate Representation (IR) for the Lean compiler.

pub mod bytecode;
pub mod instruction;
pub mod value;

pub use bytecode::IntermediateBytecode;
pub use instruction::IntermediateInstruction;
pub use value::IntermediateValue;
