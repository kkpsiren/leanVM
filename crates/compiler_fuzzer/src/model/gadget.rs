//! A *gadget*: a self-contained block of zkDSL that reads its own hint buffer, does some
//! computation, and ends in exactly one target check. Gadgets use globally-unique variable
//! names and freshly-allocated arrays, so composing many of them into one `main()` keeps them
//! independent — perturbing one gadget's buffer can only make *its* check fail.
//!
//! Each gadget knows how to:
//! - emit its zkDSL ([`Gadget::emit`]),
//! - produce an honest buffer that makes its check pass ([`Gadget::honest_buffer`]),
//! - produce a buffer that makes *only* its check fail ([`Gadget::violating_buffer`]).

use crate::field_util::{P, add_mod, rand_canonical, rand_canonical_nonzero};
use crate::harness::CheckKind;
use crate::rng::Rng;

use super::comp::Computation;
use super::emit::Emitter;

/// Upper bound for range-check constants, chosen so a violating value stays a valid address
/// (`< 2^16`) and the sound-bound precondition (`bound <= 2^16`) holds.
pub const RANGE_MAX: u64 = (1 << 16) - 2;

/// The shape of a gadget's target check.
#[derive(Debug, Clone)]
pub enum GadgetKind {
    /// `assert value == exp` where `exp` is an independent buffer cell (surfaces as a
    /// write-once `MemoryAlreadySet` on violation). Exercises the assert-fusion passes.
    EqBound,
    /// `assert (value + bal) == C` for a compile-time constant `C` (surfaces as `NotEqual`).
    EqConst { c: u64 },
    /// `assert value != other` where `other` is an independent buffer cell.
    Ne,
    /// `b = buf[0]; assert b * (b - 1) == 0` — the canonical boolean constraint.
    Bool,
    /// `assert value < bound`.
    RangeLt { bound: u64 },
    /// `assert value <= bound`.
    RangeLe { bound: u64 },
}

/// A gadget instance: a kind plus the computation feeding its check.
#[derive(Debug, Clone)]
pub struct Gadget {
    pub id: usize,
    pub kind: GadgetKind,
    pub comp: Computation,
}

impl Gadget {
    #[must_use]
    pub fn prefix(&self) -> String {
        format!("g{}_", self.id)
    }

    /// Number of inputs the computation reads (for `Bool`/range this is fixed at 1).
    #[must_use]
    pub fn n_inputs(&self) -> usize {
        match self.kind {
            GadgetKind::Bool | GadgetKind::RangeLt { .. } | GadgetKind::RangeLe { .. } => 1,
            _ => self.comp.n_inputs,
        }
    }

    /// Total hint-buffer length the gadget consumes.
    #[must_use]
    pub fn buf_len(&self) -> usize {
        match self.kind {
            GadgetKind::EqBound | GadgetKind::EqConst { .. } | GadgetKind::Ne => self.comp.n_inputs + 1,
            GadgetKind::Bool | GadgetKind::RangeLt { .. } | GadgetKind::RangeLe { .. } => 1,
        }
    }

    #[must_use]
    pub fn check_kind(&self) -> CheckKind {
        match self.kind {
            GadgetKind::EqBound | GadgetKind::EqConst { .. } | GadgetKind::Bool => CheckKind::Eq,
            GadgetKind::Ne => CheckKind::Ne,
            GadgetKind::RangeLt { .. } => CheckKind::Lt,
            GadgetKind::RangeLe { .. } => CheckKind::Le,
        }
    }

    /// One-line human description, used in findings.
    #[must_use]
    pub fn label(&self) -> String {
        let k = match &self.kind {
            GadgetKind::EqBound => "EqBound (value == buf[])".to_string(),
            GadgetKind::EqConst { c } => format!("EqConst (value == {c})"),
            GadgetKind::Ne => "Ne (value != buf[])".to_string(),
            GadgetKind::Bool => "Bool (b*(b-1) == 0)".to_string(),
            GadgetKind::RangeLt { bound } => format!("RangeLt (value < {bound})"),
            GadgetKind::RangeLe { bound } => format!("RangeLe (value <= {bound})"),
        };
        format!("g{}: {k}", self.id)
    }

    fn emit_buffer_and_inputs(&self, e: &mut Emitter, p: &str) {
        e.line(&format!("{p}buf = Array({})", self.buf_len()));
        e.line(&format!("hint_witness(\"fuzz\", {p}buf)"));
        for k in 0..self.n_inputs() {
            e.line(&format!("{p}in{k} = {p}buf[{k}]"));
        }
    }

    /// Emit the full gadget block at the emitter's current depth.
    pub fn emit(&self, e: &mut Emitter) {
        let p = self.prefix();
        e.line(&format!("# --- {} ---", self.label()));
        self.emit_buffer_and_inputs(e, &p);
        match &self.kind {
            GadgetKind::EqBound => {
                let value = self.comp.emit(e, &p);
                let exp_idx = self.comp.n_inputs;
                e.line(&format!("{p}exp = {p}buf[{exp_idx}]"));
                e.line(&format!("assert {value} == {p}exp"));
            }
            GadgetKind::EqConst { c } => {
                let base = self.comp.emit(e, &p);
                let bal_idx = self.comp.n_inputs;
                e.line(&format!("{p}bal = {p}buf[{bal_idx}]"));
                e.line(&format!("{p}val = {base} + {p}bal"));
                e.line(&format!("assert {p}val == {c}"));
            }
            GadgetKind::Ne => {
                let value = self.comp.emit(e, &p);
                let other_idx = self.comp.n_inputs;
                e.line(&format!("{p}other = {p}buf[{other_idx}]"));
                e.line(&format!("assert {value} != {p}other"));
            }
            GadgetKind::Bool => {
                e.line(&format!("{p}bm1 = {p}in0 - 1"));
                e.line(&format!("{p}prod = {p}in0 * {p}bm1"));
                e.line(&format!("assert {p}prod == 0"));
            }
            GadgetKind::RangeLt { bound } => {
                let value = self.comp.emit(e, &p);
                e.line(&format!("assert {value} < {bound}"));
            }
            GadgetKind::RangeLe { bound } => {
                let value = self.comp.emit(e, &p);
                e.line(&format!("assert {value} <= {bound}"));
            }
        }
    }

    /// A buffer making this gadget's check pass.
    #[must_use]
    pub fn honest_buffer(&self, rng: &mut Rng) -> Vec<u64> {
        match &self.kind {
            GadgetKind::EqBound => {
                let inputs: Vec<u64> = (0..self.comp.n_inputs).map(|_| rand_canonical(rng)).collect();
                let value = self.comp.eval(&inputs);
                let mut buf = inputs;
                buf.push(value);
                buf
            }
            GadgetKind::EqConst { c } => {
                let inputs: Vec<u64> = (0..self.comp.n_inputs).map(|_| rand_canonical(rng)).collect();
                let base = self.comp.eval(&inputs);
                let bal = crate::field_util::sub_mod(*c, base);
                let mut buf = inputs;
                buf.push(bal);
                buf
            }
            GadgetKind::Ne => {
                let inputs: Vec<u64> = (0..self.comp.n_inputs).map(|_| rand_canonical(rng)).collect();
                let value = self.comp.eval(&inputs);
                let other = add_mod(value, rand_canonical_nonzero(rng));
                let mut buf = inputs;
                buf.push(other);
                buf
            }
            GadgetKind::Bool => vec![u64::from(rng.flip())],
            GadgetKind::RangeLt { bound } => vec![rng.below(*bound as usize) as u64],
            GadgetKind::RangeLe { bound } => vec![rng.below(*bound as usize + 1) as u64],
        }
    }

    /// A buffer that makes *only this* check fail, derived from an honest buffer so it differs
    /// minimally. Returns the violating buffer.
    #[must_use]
    pub fn violating_buffer(&self, honest: &[u64]) -> Vec<u64> {
        let mut buf = honest.to_vec();
        match &self.kind {
            GadgetKind::EqBound => {
                let i = self.comp.n_inputs;
                buf[i] = add_mod(buf[i], 1); // exp no longer equals value
            }
            GadgetKind::EqConst { .. } => {
                let i = self.comp.n_inputs;
                buf[i] = add_mod(buf[i], 1); // bal shifted by 1 ⇒ value == C+1
            }
            GadgetKind::Ne => {
                let i = self.comp.n_inputs;
                let value = self.comp.eval(&honest[..self.comp.n_inputs]);
                buf[i] = value; // other now equals value ⇒ `!=` fails
            }
            GadgetKind::Bool => {
                buf[0] = 2 + rand_canonical_nonzero(&mut Rng::new(self.id as u64)) % (P - 2);
            }
            GadgetKind::RangeLt { bound } => {
                buf[0] = *bound; // value == bound ⇒ `< bound` fails
            }
            GadgetKind::RangeLe { bound } => {
                buf[0] = *bound + 1; // value == bound+1 ⇒ `<= bound` fails
            }
        }
        buf
    }
}
