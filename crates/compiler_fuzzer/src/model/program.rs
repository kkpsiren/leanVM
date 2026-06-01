//! A whole generated program: an ordered list of independent gadgets composed into `main()`,
//! plus the machinery to build the honest witness and per-gadget violating witnesses.

use std::collections::HashMap;

use lean_vm::{ExecutionWitness, F};

use crate::field_util::f;
use crate::rng::Rng;

use super::emit::Emitter;
use super::gadget::Gadget;

/// The single hint label every gadget draws its buffer from; buffers are consumed in gadget
/// order, so gadget `i` reads buffer `i`.
pub const HINT_LABEL: &str = "fuzz";

/// A composed, runnable checked program.
#[derive(Debug, Clone)]
pub struct CheckedProgram {
    pub gadgets: Vec<Gadget>,
}

impl CheckedProgram {
    #[must_use]
    pub const fn new(gadgets: Vec<Gadget>) -> Self {
        Self { gadgets }
    }

    /// Emit the full zkDSL source.
    #[must_use]
    pub fn emit_source(&self) -> String {
        let mut e = Emitter::new();
        e.line("from snark_lib import *");
        e.blank();
        e.line("def main():");
        e.indented(|e| {
            for g in &self.gadgets {
                g.emit(e);
            }
            e.line("return");
        });
        e.finish()
    }

    /// One honest buffer per gadget (in consumption order).
    #[must_use]
    pub fn honest_buffers(&self, rng: &mut Rng) -> Vec<Vec<u64>> {
        self.gadgets.iter().map(|g| g.honest_buffer(rng)).collect()
    }

    /// Buffers identical to `honest` except gadget `i`'s, which is replaced by a buffer that
    /// makes only gadget `i`'s check fail.
    #[must_use]
    pub fn violating_buffers(&self, honest: &[Vec<u64>], i: usize) -> Vec<Vec<u64>> {
        let mut bufs = honest.to_vec();
        bufs[i] = self.gadgets[i].violating_buffer(&honest[i]);
        bufs
    }

    /// Build an [`ExecutionWitness`] registering the given buffers under [`HINT_LABEL`].
    #[must_use]
    pub fn witness(buffers: &[Vec<u64>]) -> ExecutionWitness {
        let fuzz: Vec<Vec<F>> = buffers.iter().map(|b| b.iter().map(|&v| f(v)).collect()).collect();
        let mut hints = HashMap::new();
        hints.insert(HINT_LABEL.to_string(), fuzz);
        ExecutionWitness {
            hints,
            ..Default::default()
        }
    }
}
