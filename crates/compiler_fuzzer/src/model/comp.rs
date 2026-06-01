//! A small straight-line field computation — the "complicated stuff" a gadget does before
//! its target check. It is both emitted as zkDSL and evaluated by a reference interpreter
//! over canonical integers mod `p`, so the model knows the honest value of the computation
//! and can build witnesses that make a check pass or fail by construction.

use crate::field_util::{add_mod, mul_mod, sub_mod};

use super::emit::Emitter;

/// A binary field operation. (Division is excluded — it is undefined on zero and is exercised
/// separately via the `hint_div_floor` gadgets.)
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Op {
    Add,
    Sub,
    Mul,
}

impl Op {
    #[must_use]
    pub const fn symbol(self) -> &'static str {
        match self {
            Self::Add => "+",
            Self::Sub => "-",
            Self::Mul => "*",
        }
    }

    #[must_use]
    pub fn apply(self, a: u64, b: u64) -> u64 {
        match self {
            Self::Add => add_mod(a, b),
            Self::Sub => sub_mod(a, b),
            Self::Mul => mul_mod(a, b),
        }
    }
}

/// An operand of a computation step.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Operand {
    /// The `k`-th input the gadget reads from its hint buffer.
    Input(usize),
    /// The result of an earlier step.
    Temp(usize),
    /// A compile-time constant (canonical integer).
    Const(u64),
}

/// One SSA-style step: `temp[i] = a op b`.
#[derive(Debug, Clone, Copy)]
pub struct Step {
    pub op: Op,
    pub a: Operand,
    pub b: Operand,
}

/// A straight-line computation reading `n_inputs` inputs and producing a single value (the last
/// step's result, or `Input(0)` when there are no steps).
#[derive(Debug, Clone)]
pub struct Computation {
    pub n_inputs: usize,
    pub steps: Vec<Step>,
}

impl Computation {
    /// The identity computation: value is `Input(0)`.
    #[must_use]
    pub fn identity(n_inputs: usize) -> Self {
        debug_assert!(n_inputs >= 1);
        Self {
            n_inputs,
            steps: Vec::new(),
        }
    }

    fn operand_value(op: Operand, inputs: &[u64], temps: &[u64]) -> u64 {
        match op {
            Operand::Input(k) => inputs[k],
            Operand::Temp(t) => temps[t],
            Operand::Const(c) => c,
        }
    }

    /// Evaluate to the canonical integer value of the computation given its inputs.
    #[must_use]
    pub fn eval(&self, inputs: &[u64]) -> u64 {
        let mut temps = Vec::with_capacity(self.steps.len());
        for step in &self.steps {
            let a = Self::operand_value(step.a, inputs, &temps);
            let b = Self::operand_value(step.b, inputs, &temps);
            temps.push(step.op.apply(a, b));
        }
        temps.last().copied().unwrap_or_else(|| inputs[0])
    }

    fn operand_name(op: Operand, prefix: &str) -> String {
        match op {
            Operand::Input(k) => format!("{prefix}in{k}"),
            Operand::Temp(t) => format!("{prefix}t{t}"),
            Operand::Const(c) => format!("{c}"),
        }
    }

    /// Emit the step assignments. Inputs must already be bound to `{prefix}in{k}` by the caller.
    /// Returns the name of the variable holding the computed value.
    pub fn emit(&self, e: &mut Emitter, prefix: &str) -> String {
        for (i, step) in self.steps.iter().enumerate() {
            let a = Self::operand_name(step.a, prefix);
            let b = Self::operand_name(step.b, prefix);
            e.line(&format!("{prefix}t{i} = {a} {} {b}", step.op.symbol()));
        }
        match self.steps.len() {
            0 => format!("{prefix}in0"),
            n => format!("{prefix}t{}", n - 1),
        }
    }
}
