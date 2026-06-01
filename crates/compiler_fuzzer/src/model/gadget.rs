//! A *gadget*: a self-contained block of zkDSL that reads its own hint buffer, does some
//! computation, and ends in exactly one target check. Gadgets use globally-unique variable
//! names and freshly-allocated arrays, so composing many of them into one `main()` keeps them
//! independent — perturbing one gadget's buffer can only make *its* target check fail.
//!
//! The kinds deliberately span the compiler's harder lowering paths — `if` branches, `range`
//! loops (→ recursion + mutable-buffer rewriting), `match_range` expansion, `@inline`
//! expansion, and custom-hint-then-constrain — because that is where over-aggressive
//! simplification has historically dropped checks.
//!
//! Each gadget knows how to:
//! - emit its zkDSL ([`Gadget::emit`]) and any top-level helper functions it needs
//!   ([`Gadget::helpers`]),
//! - produce an honest buffer that makes its check pass ([`Gadget::honest_buffer`]),
//! - produce a buffer that makes *only* its check fail ([`Gadget::violating_buffer`]).

use crate::field_util::{P, add_mod, mul_mod, rand_canonical, rand_canonical_nonzero, sub_mod};
use crate::harness::CheckKind;
use crate::rng::Rng;

use super::comp::Computation;
use super::emit::Emitter;

/// Upper bound for range-check constants, chosen so a violating value stays a valid address
/// (`< 2^16`) and the sound-bound precondition (`bound <= 2^16`) holds.
pub const RANGE_MAX: u64 = (1 << 16) - 2;

/// `@inline` identity used by [`GadgetKind::InlineWrapped`].
const HELPER_ID: (&str, &str) = ("fz_id", "@inline\ndef fz_id(x):\n    return x + 0\n");
/// Square helper dispatched to by [`GadgetKind::MatchDispatch`].
const HELPER_SQUARE: (&str, &str) = ("fz_square", "def fz_square(n):\n    return n * n\n");

/// The shape of a gadget's target check. Every kind's target is an equality except the range
/// kinds, so a violating witness perturbs one independent buffer cell.
#[derive(Debug, Clone)]
pub enum GadgetKind {
    /// `assert value == exp` where `exp` is an independent buffer cell (write-once enforcement).
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
    /// The equality check lives inside a taken `if` branch (control-flow coverage).
    IfThen,
    /// `value` is accumulated by a `range` loop (loop→recursion + mutable-buffer coverage).
    Loop,
    /// `value` comes from a `match_range` dispatch to a const helper (match-expansion coverage).
    MatchDispatch { m: u64 },
    /// `value` is routed through an `@inline` function before the check (inlining coverage).
    InlineWrapped,
    /// `hint_div_floor` + correctness asserts; the target compares the quotient to an
    /// independent input (custom-hint-then-constrain coverage).
    HintDiv { d: u64 },
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

    /// Number of inputs the computation reads (for non-arithmetic kinds, fixed).
    #[must_use]
    pub fn comp_inputs(&self) -> usize {
        self.comp.n_inputs
    }

    /// Total hint-buffer length the gadget consumes.
    #[must_use]
    pub fn buf_len(&self) -> usize {
        match self.kind {
            GadgetKind::EqBound | GadgetKind::EqConst { .. } | GadgetKind::Ne | GadgetKind::InlineWrapped => {
                self.comp.n_inputs + 1
            }
            GadgetKind::IfThen => self.comp.n_inputs + 2,
            GadgetKind::Loop => self.comp.n_inputs + 1,
            GadgetKind::Bool => 1,
            GadgetKind::RangeLt { .. } | GadgetKind::RangeLe { .. } => 1,
            GadgetKind::MatchDispatch { .. } | GadgetKind::HintDiv { .. } => 2,
        }
    }

    #[must_use]
    pub fn check_kind(&self) -> CheckKind {
        match self.kind {
            GadgetKind::Ne => CheckKind::Ne,
            GadgetKind::RangeLt { .. } => CheckKind::Lt,
            GadgetKind::RangeLe { .. } => CheckKind::Le,
            _ => CheckKind::Eq,
        }
    }

    /// Top-level helper functions this gadget's emitted code calls.
    #[must_use]
    pub fn helpers(&self) -> &'static [(&'static str, &'static str)] {
        match self.kind {
            GadgetKind::InlineWrapped => std::slice::from_ref(&HELPER_ID),
            GadgetKind::MatchDispatch { .. } => std::slice::from_ref(&HELPER_SQUARE),
            _ => &[],
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
            GadgetKind::IfThen => "IfThen (assert in if-branch)".to_string(),
            GadgetKind::Loop => "Loop (range-loop sum == buf[])".to_string(),
            GadgetKind::MatchDispatch { m } => format!("MatchDispatch (match_range 0..{m})"),
            GadgetKind::InlineWrapped => "InlineWrapped (value via @inline)".to_string(),
            GadgetKind::HintDiv { d } => format!("HintDiv (q of a/{d} == buf[])"),
        };
        format!("g{}: {k}", self.id)
    }

    fn emit_buffer(&self, e: &mut Emitter, p: &str) {
        e.line(&format!("{p}buf = Array({})", self.buf_len()));
        e.line(&format!("hint_witness(\"fuzz\", {p}buf)"));
    }

    fn emit_input_reads(&self, e: &mut Emitter, p: &str, n: usize) {
        for k in 0..n {
            e.line(&format!("{p}in{k} = {p}buf[{k}]"));
        }
    }

    /// Emit the full gadget block at the emitter's current depth.
    pub fn emit(&self, e: &mut Emitter) {
        let p = self.prefix();
        e.line(&format!("# --- {} ---", self.label()));
        self.emit_buffer(e, &p);
        let n = self.comp.n_inputs;
        match &self.kind {
            GadgetKind::EqBound => {
                self.emit_input_reads(e, &p, n);
                let value = self.comp.emit(e, &p);
                e.line(&format!("{p}exp = {p}buf[{n}]"));
                e.line(&format!("assert {value} == {p}exp"));
            }
            GadgetKind::EqConst { c } => {
                self.emit_input_reads(e, &p, n);
                let base = self.comp.emit(e, &p);
                e.line(&format!("{p}bal = {p}buf[{n}]"));
                e.line(&format!("{p}val = {base} + {p}bal"));
                e.line(&format!("assert {p}val == {c}"));
            }
            GadgetKind::Ne => {
                self.emit_input_reads(e, &p, n);
                let value = self.comp.emit(e, &p);
                e.line(&format!("{p}other = {p}buf[{n}]"));
                e.line(&format!("assert {value} != {p}other"));
            }
            GadgetKind::Bool => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("{p}bm1 = {p}in0 - 1"));
                e.line(&format!("{p}prod = {p}in0 * {p}bm1"));
                e.line(&format!("assert {p}prod == 0"));
            }
            GadgetKind::RangeLt { bound } => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("assert {p}in0 < {bound}"));
            }
            GadgetKind::RangeLe { bound } => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("assert {p}in0 <= {bound}"));
            }
            GadgetKind::IfThen => {
                e.line(&format!("{p}sel = {p}buf[{}]", n + 1));
                e.line(&format!("if {p}sel == 1:"));
                e.indented(|e| {
                    self.emit_input_reads(e, &p, n);
                    let value = self.comp.emit(e, &p);
                    e.line(&format!("{p}exp = {p}buf[{n}]"));
                    e.line(&format!("assert {value} == {p}exp"));
                });
            }
            GadgetKind::Loop => {
                e.line(&format!("{p}acc: Mut = 0"));
                e.line(&format!("for {p}i in range(0, {n}):"));
                e.indented(|e| {
                    e.line(&format!("{p}acc = {p}acc + {p}buf[{p}i]"));
                });
                e.line(&format!("{p}exp = {p}buf[{n}]"));
                e.line(&format!("assert {p}acc == {p}exp"));
            }
            GadgetKind::MatchDispatch { m } => {
                e.line(&format!("{p}sel = {p}buf[0]"));
                e.line(&format!(
                    "{p}res = match_range({p}sel, range(0, {m}), lambda {p}i: fz_square({p}i))"
                ));
                e.line(&format!("{p}exp = {p}buf[1]"));
                e.line(&format!("assert {p}res == {p}exp"));
            }
            GadgetKind::InlineWrapped => {
                self.emit_input_reads(e, &p, n);
                let value = self.comp.emit(e, &p);
                e.line(&format!("{p}w = fz_id({value})"));
                e.line(&format!("{p}exp = {p}buf[{n}]"));
                e.line(&format!("assert {p}w == {p}exp"));
            }
            GadgetKind::HintDiv { d } => {
                e.line(&format!("{p}a = {p}buf[0]"));
                e.line(&format!("{p}q: Imm"));
                e.line(&format!("{p}r: Imm"));
                e.line(&format!("hint_div_floor({p}a, {d}, {p}q, {p}r)"));
                e.line(&format!("assert {p}r < {d}"));
                e.line(&format!("assert {p}q * {d} + {p}r == {p}a"));
                e.line(&format!("{p}exp = {p}buf[1]"));
                e.line(&format!("assert {p}q == {p}exp"));
            }
        }
    }

    /// A buffer making this gadget's check pass.
    #[must_use]
    pub fn honest_buffer(&self, rng: &mut Rng) -> Vec<u64> {
        let n = self.comp.n_inputs;
        match &self.kind {
            GadgetKind::EqBound | GadgetKind::InlineWrapped => {
                let inputs: Vec<u64> = (0..n).map(|_| rand_canonical(rng)).collect();
                let value = self.comp.eval(&inputs);
                let mut buf = inputs;
                buf.push(value);
                buf
            }
            GadgetKind::EqConst { c } => {
                let inputs: Vec<u64> = (0..n).map(|_| rand_canonical(rng)).collect();
                let base = self.comp.eval(&inputs);
                let mut buf = inputs;
                buf.push(sub_mod(*c, base));
                buf
            }
            GadgetKind::Ne => {
                let inputs: Vec<u64> = (0..n).map(|_| rand_canonical(rng)).collect();
                let value = self.comp.eval(&inputs);
                let other = add_mod(value, rand_canonical_nonzero(rng));
                let mut buf = inputs;
                buf.push(other);
                buf
            }
            GadgetKind::Bool => vec![u64::from(rng.flip())],
            GadgetKind::RangeLt { bound } => vec![rng.below(*bound as usize) as u64],
            GadgetKind::RangeLe { bound } => vec![rng.below(*bound as usize + 1) as u64],
            GadgetKind::IfThen => {
                let inputs: Vec<u64> = (0..n).map(|_| rand_canonical(rng)).collect();
                let value = self.comp.eval(&inputs);
                let mut buf = inputs;
                buf.push(value); // exp
                buf.push(1); // sel: take the branch
                buf
            }
            GadgetKind::Loop => {
                let inputs: Vec<u64> = (0..n).map(|_| rand_canonical(rng)).collect();
                let sum = inputs.iter().fold(0u64, |a, &b| add_mod(a, b));
                let mut buf = inputs;
                buf.push(sum);
                buf
            }
            GadgetKind::MatchDispatch { m } => {
                let sel = rng.below(*m as usize) as u64;
                vec![sel, mul_mod(sel, sel)]
            }
            GadgetKind::HintDiv { d } => {
                let a = rng.below(*d as usize * 1000) as u64;
                vec![a, a / d]
            }
        }
    }

    /// A buffer that makes *only this* check fail, derived from an honest buffer.
    #[must_use]
    pub fn violating_buffer(&self, honest: &[u64]) -> Vec<u64> {
        let mut buf = honest.to_vec();
        let n = self.comp.n_inputs;
        match &self.kind {
            // Perturb the dedicated "expected" cell so only the target equality fails.
            GadgetKind::EqBound
            | GadgetKind::EqConst { .. }
            | GadgetKind::InlineWrapped
            | GadgetKind::IfThen
            | GadgetKind::Loop => {
                buf[n] = add_mod(buf[n], 1);
            }
            GadgetKind::MatchDispatch { .. } | GadgetKind::HintDiv { .. } => {
                buf[1] = add_mod(buf[1], 1);
            }
            GadgetKind::Ne => {
                buf[n] = self.comp.eval(&honest[..n]); // other := value ⇒ `!=` fails
            }
            GadgetKind::Bool => {
                buf[0] = 2 + rand_canonical_nonzero(&mut Rng::new(self.id as u64)) % (P - 2);
            }
            GadgetKind::RangeLt { bound } => buf[0] = *bound,
            GadgetKind::RangeLe { bound } => buf[0] = *bound + 1,
        }
        buf
    }
}
