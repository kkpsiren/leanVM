//! Lean VM - A minimal virtual machine implementation

pub mod buffer_pool;
mod core;
mod diagnostics;
mod execution;
mod isa;
mod tables;

pub use core::*;
pub use diagnostics::*;
pub use execution::*;
pub use isa::*;
pub use tables::*;
