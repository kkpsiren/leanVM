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

use lean_vm::DIMENSION;

use crate::field_util::{
    ExtMode, ExtOp, P, add_mod, div_canonical, ext_a_len, ext_op_eval, mul_mod, poseidon16_compress_half,
    rand_canonical, rand_canonical_nonzero, sub_mod,
};
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
/// Tuple-returning helper used by [`GadgetKind::MultiReturn`] (exercises multi-value return +
/// tuple unpacking).
const HELPER_PAIR: (&str, &str) = ("fz_pair", "def fz_pair(x):\n    return x + 1, x + 2\n");

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
    /// `n` distinct `assert buf[i] < bound` checks inside an `unroll` loop. Each iteration must
    /// leave behind its own range-check lowering (2 `DerefHint`s); the structural oracle requires
    /// the full `2*n`, so an over-aggressive CSE/fusion that collapses iterations is caught even
    /// though a runtime witness (rejected by the surviving companion) would mask it. `n` violations.
    UnrolledRangeLt { n: usize, bound: u64 },
    /// The equality check lives inside a taken `if` branch (control-flow coverage).
    IfThen,
    /// `value` is accumulated by a `range` loop (loop→recursion + mutable-buffer coverage).
    Loop,
    /// `value` comes from a `match_range` dispatch to a const helper (match-expansion coverage).
    MatchDispatch { m: u64 },
    /// `value` comes from a *chained* `match_range` with two contiguous ranges and distinct arm
    /// bodies (`0..2 ↦ i*10`, `2..5 ↦ i*100`). Exercises the multi-(range, lambda) expansion path
    /// that the single-range `MatchDispatch` never reaches; the selector picks which arm runs.
    MatchChained,
    /// `value` is routed through an `@inline` function before the check (inlining coverage).
    InlineWrapped,
    /// `hint_div_floor` + correctness asserts; the target compares the quotient to an
    /// independent input (custom-hint-then-constrain coverage).
    HintDiv { d: u64 },
    /// `v = in0 + 0; assert v == exp` — targets copy-propagation (`v = mem + 0` is rewritten
    /// away). The assert must survive the rewrite.
    CopyPropEq,
    /// Two identical subexpressions (`in0 * in1`) each asserted against its own bound. Targets
    /// common-subexpression elimination: CSE collapses the second into the first, and *both*
    /// asserts must remain enforced. Two independent violations.
    CseEq,
    /// `v = buf[0]; w = buf[1]; assert v == w` — both sides are one-time memory reads, the exact
    /// shape `fuse_raw_asserts` rewrites. The equality must survive.
    TwoReadsEq,
    /// A running sum `b_k = b_{k-1} + d_k` with an independent checkpoint `assert b_k == c_k` at
    /// every step. Stresses repeated assert-fusion / copy-propagation along a dependency chain;
    /// each of the `len` checkpoints is an independent violation.
    RunningChain { len: usize },
    /// An extension-field precompile (`add`/`dot`/`poly_eq` in `ee`/`be` mode, length `n`), then
    /// assert the 5-coordinate result equals an independent buffer value (precompile lowering +
    /// multi-cell equality). `DIMENSION` independent violations.
    ExtOp { op: ExtOp, mode: ExtMode, n: usize },
    /// The Poseidon2 compression precompile: `poseidon16_compress_half(left, right, out)` over a
    /// 16-element input, then assert the 8-element output equals an independent buffer region. The
    /// fuzzer never exercised any Poseidon precompile before; the reference output is computed by
    /// `field_util::poseidon16_compress_half`. `DIGEST_LEN` (8) independent violations.
    Poseidon,
    /// An equality check nested inside an `if` inside a runtime `range` loop, over `n` independent
    /// (value, expected) pairs. Stresses assert survival through if-in-loop nesting and
    /// loop→recursion. `n` independent violations.
    NestedIfLoop { n: usize },
    /// Two array chains accumulated across an `outer`×`inner` nested `range` loop (indexed by the
    /// flattened `i*inner + j`), each reading the previous iteration's cell and checked after the
    /// loop. Stresses cross-iteration array data-dependencies through nested loop→recursion — the
    /// buffer-based replacement for loop-carried mutables, which the compiler now forbids. Two
    /// independent violations (one per chain).
    NestedMutLoop { outer: usize, inner: usize },
    /// `n` prover-supplied bits, each constrained boolean (`b*(b-1)==0`) and reconstructed
    /// (`acc = acc*2 + b`), with a final `assert acc == expected`. This is the canonical
    /// hint-then-constrain decomposition pattern (XMSS / range proofs); every boolean **and** the
    /// reconstruction must survive. `n + 1` independent violations (each bit, then the sum).
    BitDecomp { n: usize },
    /// `assert False` inside a taken `if` branch (Panic lowering behind control flow). The honest
    /// witness leaves the branch untaken; the violating witness takes it.
    Panic,
    /// `debug_assert(value < bound)` — a prover-side check the honest runner still enforces. It
    /// emits *no* bytecode, so only the runtime oracle can confirm it survives.
    DebugAssertLt { bound: u64 },
    /// The target equality lives in the `else` branch of an `if`/`else` (else-branch lowering).
    IfElse,
    /// `x: Mut = a; x += b; x *= c; assert x == exp` — compound-assignment (`+=`, `*=`) lowering.
    CompoundAssign,
    /// `q = a / b; assert q == exp` — runtime field division (`/`) lowering. `b` is non-zero.
    Div,
    /// `p, q = fz_pair(in); assert p == e1; assert q == e2` — multi-value return + tuple unpack.
    /// Two independent violations.
    MultiReturn,
    /// `arr[base + K]` with a runtime `base` and compile-time `K` — exercises the
    /// `fold_const_offset_into_deref` simplifier pass; the read value must still equal the cell it
    /// addresses.
    PointerOffset,
    /// `arr[base - K]` with a *non-zero* runtime `base` and compile-time `K` — the subtraction
    /// offset takes a different `fold_const_offset_into_deref` path than `PointerOffset`'s addition;
    /// the read must still address `base - K`.
    PointerOffsetSub,
    /// A `parallel_range` loop whose body asserts `value == expected` over `n` independent pairs
    /// (parallel-loop lowering; exercises the `ParallelSegmentFailed` path). `n` violations.
    ParallelLoop { n: usize },
    /// `assert v == <compile-time const expression>` where the expression mixes `**`, `%`,
    /// `div_floor`/`div_ceil`, `saturating_sub`, `next_multiple_of`, `log2_ceil`. The honest buffer
    /// holds an *independent* reference value: a miscompiled constant fold makes the honest witness
    /// fail. `src` is the emitted expression, `value` its independent reference.
    ConstFold { src: String, value: u64 },
    /// An immutable forward declaration `x: Imm` assigned on *both* branches of an `if`/`else`
    /// (each from a different cell), then `assert x == exp`. Exercises forward-declaration +
    /// conditional (mutually-exclusive write-once) assignment + a post-branch equality. The check
    /// genuinely constrains `x`, so a perturbed `exp` must be rejected.
    ForwardDeclEq,
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
            GadgetKind::UnrolledRangeLt { n, .. } => n,
            GadgetKind::MatchDispatch { .. } | GadgetKind::HintDiv { .. } | GadgetKind::MatchChained => 2,
            GadgetKind::CopyPropEq | GadgetKind::TwoReadsEq => 2,
            GadgetKind::CseEq => 4,
            GadgetKind::RunningChain { len } => 2 * len,
            GadgetKind::ExtOp { mode, n, .. } => ext_a_len(mode, n) + n * DIMENSION + DIMENSION,
            GadgetKind::Poseidon => 24, // left(8) | right(8) | expected output(8)
            GadgetKind::NestedIfLoop { n } => 2 * n + 1,
            GadgetKind::NestedMutLoop { .. } => 6, // a0, b0, da, db, exp_a, exp_b
            GadgetKind::BitDecomp { n } => n + 1,
            GadgetKind::Panic | GadgetKind::DebugAssertLt { .. } | GadgetKind::ConstFold { .. } => 1,
            GadgetKind::IfElse => self.comp.n_inputs + 2,
            GadgetKind::CompoundAssign => 4,
            GadgetKind::Div | GadgetKind::MultiReturn => 3,
            GadgetKind::PointerOffset | GadgetKind::PointerOffsetSub => 10,
            GadgetKind::ParallelLoop { n } => 2 * n,
            GadgetKind::ForwardDeclEq => 4,
        }
    }

    /// How many independently-breakable checks this gadget enforces. A violation index `k` in
    /// `0..n_violations()` selects which one [`Gadget::violating_buffer`] breaks.
    #[must_use]
    pub fn n_violations(&self) -> usize {
        match self.kind {
            // CseEq: 2 expected-cell breaks + 2 input-side breaks (perturb a shared operand, not
            // the dedicated `exp` cell — catches a check silently bound to the wrong operand).
            GadgetKind::CseEq => 4,
            GadgetKind::MultiReturn => 2,
            // TwoReadsEq: break each side of `v == w` independently (wrong-operand detection).
            GadgetKind::TwoReadsEq => 2,
            // RunningChain: one break per checkpoint + one input-side break of the base value.
            GadgetKind::RunningChain { len } => len + 1,
            GadgetKind::ExtOp { .. } => DIMENSION,
            GadgetKind::Poseidon => 8, // one per output coordinate
            GadgetKind::NestedIfLoop { n } | GadgetKind::ParallelLoop { n } => n,
            GadgetKind::NestedMutLoop { .. } => 2, // one per carried mutable
            GadgetKind::UnrolledRangeLt { n, .. } => n,
            GadgetKind::BitDecomp { n } => n + 1,
            _ => 1,
        }
    }

    #[must_use]
    pub fn check_kind(&self) -> CheckKind {
        match self.kind {
            GadgetKind::Ne => CheckKind::Ne,
            GadgetKind::RangeLt { .. } | GadgetKind::UnrolledRangeLt { .. } => CheckKind::Lt,
            GadgetKind::RangeLe { .. } => CheckKind::Le,
            GadgetKind::Panic => CheckKind::Panic,
            GadgetKind::DebugAssertLt { .. } => CheckKind::Debug,
            _ => CheckKind::Eq,
        }
    }

    /// Top-level helper functions this gadget's emitted code calls.
    #[must_use]
    pub fn helpers(&self) -> &'static [(&'static str, &'static str)] {
        match self.kind {
            GadgetKind::InlineWrapped => std::slice::from_ref(&HELPER_ID),
            GadgetKind::MatchDispatch { .. } => std::slice::from_ref(&HELPER_SQUARE),
            GadgetKind::MultiReturn => std::slice::from_ref(&HELPER_PAIR),
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
            GadgetKind::UnrolledRangeLt { n, bound } => format!("UnrolledRangeLt ({n}x value < {bound})"),
            GadgetKind::IfThen => "IfThen (assert in if-branch)".to_string(),
            GadgetKind::Loop => "Loop (range-loop sum == buf[])".to_string(),
            GadgetKind::MatchDispatch { m } => format!("MatchDispatch (match_range 0..{m})"),
            GadgetKind::MatchChained => "MatchChained (two contiguous match_range arms)".to_string(),
            GadgetKind::InlineWrapped => "InlineWrapped (value via @inline)".to_string(),
            GadgetKind::HintDiv { d } => format!("HintDiv (q of a/{d} == buf[])"),
            GadgetKind::CopyPropEq => "CopyPropEq (v = x + 0; v == buf[])".to_string(),
            GadgetKind::CseEq => "CseEq (shared in0*in1, two asserts)".to_string(),
            GadgetKind::TwoReadsEq => "TwoReadsEq (buf[0] == buf[1])".to_string(),
            GadgetKind::RunningChain { len } => format!("RunningChain (len {len}, per-step checkpoints)"),
            GadgetKind::ExtOp { op, mode, n } => format!("ExtOp ({}, n {n}, result == buf[])", op.fn_name(*mode)),
            GadgetKind::Poseidon => "Poseidon (poseidon16_compress_half, 8-cell output)".to_string(),
            GadgetKind::NestedIfLoop { n } => format!("NestedIfLoop (n {n}, assert in if-in-loop)"),
            GadgetKind::NestedMutLoop { outer, inner } => {
                format!("NestedMutLoop ({outer}x{inner} nested loop, 2 carried mutables)")
            }
            GadgetKind::BitDecomp { n } => format!("BitDecomp (n {n}, bits + reconstruction)"),
            GadgetKind::Panic => "Panic (assert False in taken if)".to_string(),
            GadgetKind::DebugAssertLt { bound } => format!("DebugAssertLt (debug_assert value < {bound})"),
            GadgetKind::IfElse => "IfElse (assert in else-branch)".to_string(),
            GadgetKind::CompoundAssign => "CompoundAssign (x += b; x *= c; x == buf[])".to_string(),
            GadgetKind::Div => "Div (a / b == buf[])".to_string(),
            GadgetKind::MultiReturn => "MultiReturn (p, q = fz_pair(in))".to_string(),
            GadgetKind::PointerOffset => "PointerOffset (arr[base + K] == buf[])".to_string(),
            GadgetKind::PointerOffsetSub => "PointerOffsetSub (arr[base - K], base != 0)".to_string(),
            GadgetKind::ParallelLoop { n } => format!("ParallelLoop (n {n}, assert in parallel_range)"),
            GadgetKind::ConstFold { src, value } => format!("ConstFold (v == {src} = {value})"),
            GadgetKind::ForwardDeclEq => "ForwardDeclEq (x: Imm assigned in both branches)".to_string(),
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
            GadgetKind::UnrolledRangeLt { n, bound } => {
                // n distinct range checks, one per unrolled iteration; each must lower to its own
                // pair of DerefHints (the structural oracle counts the total).
                e.line(&format!("for {p}i in unroll(0, {n}):"));
                e.indented(|e| {
                    e.line(&format!("assert {p}buf[{p}i] < {bound}"));
                });
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
                // Loop-carried mutables in a `range` loop are no longer allowed (the compiler
                // requires an explicit buffer). Accumulate through an array chain instead:
                // acc[i+1] = acc[i] + buf[i], reading the previous iteration's cell.
                e.line(&format!("{p}acc = Array({})", n + 1));
                e.line(&format!("{p}acc[0] = 0"));
                e.line(&format!("for {p}i in range(0, {n}):"));
                e.indented(|e| {
                    e.line(&format!("{p}acc[{p}i + 1] = {p}acc[{p}i] + {p}buf[{p}i]"));
                });
                e.line(&format!("{p}exp = {p}buf[{n}]"));
                e.line(&format!("assert {p}acc[{n}] == {p}exp"));
            }
            GadgetKind::MatchDispatch { m } => {
                e.line(&format!("{p}sel = {p}buf[0]"));
                e.line(&format!(
                    "{p}res = match_range({p}sel, range(0, {m}), lambda {p}i: fz_square({p}i))"
                ));
                e.line(&format!("{p}exp = {p}buf[1]"));
                e.line(&format!("assert {p}res == {p}exp"));
            }
            GadgetKind::MatchChained => {
                // Two contiguous ranges, distinct arm bodies: 0..2 ↦ i*10, 2..5 ↦ i*100.
                e.line(&format!("{p}sel = {p}buf[0]"));
                e.line(&format!(
                    "{p}res = match_range({p}sel, range(0, 2), lambda {p}i: {p}i * 10, range(2, 5), lambda {p}i: {p}i * 100)"
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
            GadgetKind::CopyPropEq => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("{p}v = {p}in0 + 0")); // the `mem + 0` copy-propagation pattern
                e.line(&format!("{p}exp = {p}buf[1]"));
                e.line(&format!("assert {p}v == {p}exp"));
            }
            GadgetKind::CseEq => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("{p}in1 = {p}buf[1]"));
                e.line(&format!("{p}t1 = {p}in0 * {p}in1"));
                e.line(&format!("{p}exp1 = {p}buf[2]"));
                e.line(&format!("assert {p}t1 == {p}exp1"));
                e.line(&format!("{p}t2 = {p}in0 * {p}in1")); // identical subexpr → CSE-eligible
                e.line(&format!("{p}exp2 = {p}buf[3]"));
                e.line(&format!("assert {p}t2 == {p}exp2"));
            }
            GadgetKind::TwoReadsEq => {
                e.line(&format!("{p}v = {p}buf[0]"));
                e.line(&format!("{p}w = {p}buf[1]"));
                e.line(&format!("assert {p}v == {p}w"));
            }
            GadgetKind::RunningChain { len } => {
                e.line(&format!("{p}b0 = {p}buf[0]"));
                e.line(&format!("{p}c0 = {p}buf[{len}]"));
                e.line(&format!("assert {p}b0 == {p}c0"));
                for k in 1..*len {
                    e.line(&format!("{p}d{k} = {p}buf[{k}]"));
                    e.line(&format!("{p}b{k} = {p}b{} + {p}d{k}", k - 1));
                    e.line(&format!("{p}c{k} = {p}buf[{}]", len + k));
                    e.line(&format!("assert {p}b{k} == {p}c{k}"));
                }
            }
            GadgetKind::ExtOp { op, mode, n } => {
                // buf = [a (a_len) | b (n*DIM) | expected (DIM)]; res = op(a, b).
                let a_len = ext_a_len(*mode, *n);
                let fname = op.fn_name(*mode);
                e.line(&format!("{p}res = Array({DIMENSION})"));
                let call = if *n == 1 {
                    format!("{fname}({p}buf, {p}buf + {a_len}, {p}res)")
                } else {
                    format!("{fname}({p}buf, {p}buf + {a_len}, {p}res, {n})")
                };
                e.line(&call);
                e.line(&format!("for {p}i in unroll(0, {DIMENSION}):"));
                e.indented(|e| {
                    e.line(&format!(
                        "assert {p}res[{p}i] == {p}buf[{} + {p}i]",
                        a_len + n * DIMENSION
                    ));
                });
            }
            GadgetKind::Poseidon => {
                // buf = [left(8) | right(8) | expected(8)]; out = (Poseidon(left|right)+ (left|right))[0..8].
                e.line(&format!("{p}out = Array(8)"));
                e.line(&format!("poseidon16_compress_half({p}buf, {p}buf + 8, {p}out)"));
                e.line(&format!("for {p}i in unroll(0, 8):"));
                e.indented(|e| {
                    e.line(&format!("assert {p}out[{p}i] == {p}buf[16 + {p}i]"));
                });
            }
            GadgetKind::NestedIfLoop { n } => {
                // buf = [v(n) | expected(n) | sel]; sel == 1 (taken).
                e.line(&format!("{p}sel = {p}buf[{}]", 2 * n));
                e.line(&format!("for {p}i in range(0, {n}):"));
                e.indented(|e| {
                    e.line(&format!("if {p}sel == 1:"));
                    e.indented(|e| {
                        e.line(&format!("{p}v = {p}buf[{p}i]"));
                        e.line(&format!("{p}exp = {p}buf[{n} + {p}i]"));
                        e.line(&format!("assert {p}v == {p}exp"));
                    });
                });
            }
            GadgetKind::NestedMutLoop { outer, inner } => {
                // buf = [a0, b0, da, db, exp_a, exp_b]. Loop-carried mutables are no longer allowed,
                // so two array chains accumulate their per-iteration delta across the nested range
                // loop, indexed by the flattened iteration count `i*inner + j`. After outer*inner
                // iterations: chainA[k] = a0 + k*da, chainB[k] = b0 + k*db (k = outer*inner).
                let iters = outer * inner;
                e.line(&format!("{p}chainA = Array({})", iters + 1));
                e.line(&format!("{p}chainB = Array({})", iters + 1));
                e.line(&format!("{p}chainA[0] = {p}buf[0]"));
                e.line(&format!("{p}chainB[0] = {p}buf[1]"));
                e.line(&format!("for {p}i in range(0, {outer}):"));
                e.indented(|e| {
                    e.line(&format!("for {p}j in range(0, {inner}):"));
                    e.indented(|e| {
                        e.line(&format!("{p}idx = {p}i * {inner} + {p}j"));
                        e.line(&format!("{p}chainA[{p}idx + 1] = {p}chainA[{p}idx] + {p}buf[2]"));
                        e.line(&format!("{p}chainB[{p}idx + 1] = {p}chainB[{p}idx] + {p}buf[3]"));
                    });
                });
                e.line(&format!("{p}exp_a = {p}buf[4]"));
                e.line(&format!("{p}exp_b = {p}buf[5]"));
                e.line(&format!("assert {p}chainA[{iters}] == {p}exp_a"));
                e.line(&format!("assert {p}chainB[{iters}] == {p}exp_b"));
            }
            GadgetKind::BitDecomp { n } => {
                // buf = [bit_0 .. bit_{n-1} | expected]; acc = sum bit_i * 2^(n-1-i).
                e.line(&format!("{p}acc: Mut = 0"));
                e.line(&format!("for {p}i in unroll(0, {n}):"));
                e.indented(|e| {
                    e.line(&format!("assert {p}buf[{p}i] * ({p}buf[{p}i] - 1) == 0"));
                    e.line(&format!("{p}acc = {p}acc * 2 + {p}buf[{p}i]"));
                });
                e.line(&format!("{p}exp = {p}buf[{n}]"));
                e.line(&format!("assert {p}acc == {p}exp"));
            }
            GadgetKind::Panic => {
                // buf = [sel]; honest sel == 0 (branch untaken), violating sel == 1.
                e.line(&format!("{p}sel = {p}buf[0]"));
                e.line(&format!("if {p}sel == 1:"));
                e.indented(|e| {
                    e.line("assert False");
                });
            }
            GadgetKind::DebugAssertLt { bound } => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("debug_assert({p}in0 < {bound})"));
            }
            GadgetKind::IfElse => {
                // buf = [inputs(n) | exp | sel]; honest sel == 0 ⇒ else branch runs.
                e.line(&format!("{p}sel = {p}buf[{}]", n + 1));
                e.line(&format!("if {p}sel == 1:"));
                e.indented(|e| {
                    e.line(&format!("{p}skip = 0"));
                });
                e.line("else:");
                e.indented(|e| {
                    self.emit_input_reads(e, &p, n);
                    let value = self.comp.emit(e, &p);
                    e.line(&format!("{p}exp = {p}buf[{n}]"));
                    e.line(&format!("assert {value} == {p}exp"));
                });
            }
            GadgetKind::CompoundAssign => {
                e.line(&format!("{p}x: Mut = {p}buf[0]"));
                e.line(&format!("{p}x += {p}buf[1]"));
                e.line(&format!("{p}x *= {p}buf[2]"));
                e.line(&format!("{p}exp = {p}buf[3]"));
                e.line(&format!("assert {p}x == {p}exp"));
            }
            GadgetKind::Div => {
                e.line(&format!("{p}a = {p}buf[0]"));
                e.line(&format!("{p}b = {p}buf[1]"));
                e.line(&format!("{p}q = {p}a / {p}b"));
                e.line(&format!("{p}exp = {p}buf[2]"));
                e.line(&format!("assert {p}q == {p}exp"));
            }
            GadgetKind::MultiReturn => {
                e.line(&format!("{p}in0 = {p}buf[0]"));
                e.line(&format!("{p}pp, {p}qq = fz_pair({p}in0)"));
                e.line(&format!("{p}e1 = {p}buf[1]"));
                e.line(&format!("{p}e2 = {p}buf[2]"));
                e.line(&format!("assert {p}pp == {p}e1"));
                e.line(&format!("assert {p}qq == {p}e2"));
            }
            GadgetKind::PointerOffset => {
                // buf = [base(=0) | fillers(8) | expected]; reads arr[base + 3] = buf[4].
                e.line(&format!("{p}arr = Array(8)"));
                e.line(&format!("for {p}i in unroll(0, 8):"));
                e.indented(|e| {
                    e.line(&format!("{p}arr[{p}i] = {p}buf[{p}i + 1]"));
                });
                e.line(&format!("{p}base = {p}buf[0]"));
                e.line(&format!("{p}v = {p}arr[{p}base + 3]"));
                e.line(&format!("{p}exp = {p}buf[9]"));
                e.line(&format!("assert {p}v == {p}exp"));
            }
            GadgetKind::PointerOffsetSub => {
                // buf = [base(=5) | fillers(8) | expected]; reads arr[base - 2] = arr[3] = buf[4].
                e.line(&format!("{p}arr = Array(8)"));
                e.line(&format!("for {p}i in unroll(0, 8):"));
                e.indented(|e| {
                    e.line(&format!("{p}arr[{p}i] = {p}buf[{p}i + 1]"));
                });
                e.line(&format!("{p}base = {p}buf[0]"));
                e.line(&format!("{p}v = {p}arr[{p}base - 2]"));
                e.line(&format!("{p}exp = {p}buf[9]"));
                e.line(&format!("assert {p}v == {p}exp"));
            }
            GadgetKind::ParallelLoop { n } => {
                // buf = [v(n) | expected(n)]; each iteration independent (no Mut, disjoint cells).
                e.line(&format!("for {p}i in parallel_range(0, {n}):"));
                e.indented(|e| {
                    e.line(&format!("{p}v = {p}buf[{p}i]"));
                    e.line(&format!("{p}exp = {p}buf[{n} + {p}i]"));
                    e.line(&format!("assert {p}v == {p}exp"));
                });
            }
            GadgetKind::ConstFold { src, .. } => {
                e.line(&format!("{p}v = {p}buf[0]"));
                e.line(&format!("assert {p}v == ({src})"));
            }
            GadgetKind::ForwardDeclEq => {
                // buf = [a, b, sel, exp]; x is assigned on both branches (write-once is safe since
                // the branches are mutually exclusive). honest sel == 1 ⇒ x = a, exp = a.
                e.line(&format!("{p}sel = {p}buf[2]"));
                e.line(&format!("{p}x: Imm"));
                e.line(&format!("if {p}sel == 1:"));
                e.indented(|e| {
                    e.line(&format!("{p}x = {p}buf[0]"));
                });
                e.line("else:");
                e.indented(|e| {
                    e.line(&format!("{p}x = {p}buf[1]"));
                });
                e.line(&format!("{p}exp = {p}buf[3]"));
                e.line(&format!("assert {p}x == {p}exp"));
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
            GadgetKind::UnrolledRangeLt { n, bound } => (0..*n).map(|_| rng.below(*bound as usize) as u64).collect(),
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
            GadgetKind::MatchChained => {
                let sel = rng.below(5) as u64; // selector in [0, 5)
                let res = if sel < 2 { sel * 10 } else { sel * 100 };
                vec![sel, res]
            }
            GadgetKind::HintDiv { d } => {
                let a = rng.below(*d as usize * 1000) as u64;
                vec![a, a / d]
            }
            GadgetKind::CopyPropEq => {
                let x = rand_canonical(rng);
                vec![x, x] // v = x + 0 == exp(=x)
            }
            GadgetKind::CseEq => {
                // Non-zero operands so perturbing either input reliably changes the product
                // (enables the input-side violations; a zero factor would mask them).
                let (a, b) = (rand_canonical_nonzero(rng), rand_canonical_nonzero(rng));
                let prod = mul_mod(a, b);
                vec![a, b, prod, prod] // both asserts: in0*in1 == prod
            }
            GadgetKind::TwoReadsEq => {
                let v = rand_canonical(rng);
                vec![v, v]
            }
            GadgetKind::RunningChain { len } => {
                // inputs: b0, d1..d_{len-1}; checkpoints: b0, b1, ..., b_{len-1}
                let inputs: Vec<u64> = (0..*len).map(|_| rand_canonical(rng)).collect();
                let mut checkpoints = Vec::with_capacity(*len);
                let mut acc = inputs[0];
                checkpoints.push(acc);
                for &d in &inputs[1..] {
                    acc = add_mod(acc, d);
                    checkpoints.push(acc);
                }
                let mut buf = inputs;
                buf.extend(checkpoints);
                buf
            }
            GadgetKind::ExtOp { op, mode, n } => {
                let a_len = ext_a_len(*mode, *n);
                let a: Vec<u64> = (0..a_len).map(|_| rand_canonical(rng)).collect();
                let b: Vec<u64> = (0..n * DIMENSION).map(|_| rand_canonical(rng)).collect();
                let r = ext_op_eval(*op, *mode, &a, &b, *n);
                let mut buf = a;
                buf.extend(b);
                buf.extend(r);
                buf
            }
            GadgetKind::Poseidon => {
                let input: Vec<u64> = (0..16).map(|_| rand_canonical(rng)).collect();
                let out = poseidon16_compress_half(&input);
                let mut buf = input;
                buf.extend(out); // expected output region
                buf
            }
            GadgetKind::NestedIfLoop { n } => {
                let v: Vec<u64> = (0..*n).map(|_| rand_canonical(rng)).collect();
                let mut buf = v.clone();
                buf.extend(v); // expected == value
                buf.push(1); // sel: take the branch
                buf
            }
            GadgetKind::NestedMutLoop { outer, inner } => {
                let (a0, b0, da, db) = (
                    rand_canonical(rng),
                    rand_canonical(rng),
                    rand_canonical(rng),
                    rand_canonical(rng),
                );
                let iters = (outer * inner) as u64;
                let mut a = a0;
                let mut b = b0;
                for _ in 0..iters {
                    a = add_mod(a, da);
                    b = add_mod(b, db);
                }
                vec![a0, b0, da, db, a, b]
            }
            GadgetKind::BitDecomp { n } => {
                let bits: Vec<u64> = (0..*n).map(|_| u64::from(rng.flip())).collect();
                let acc = bits.iter().fold(0u64, |a, &b| add_mod(mul_mod(a, 2), b));
                let mut buf = bits;
                buf.push(acc);
                buf
            }
            GadgetKind::Panic => vec![0], // sel = 0 ⇒ branch untaken
            GadgetKind::DebugAssertLt { bound } => vec![rng.below(*bound as usize) as u64],
            GadgetKind::IfElse => {
                let inputs: Vec<u64> = (0..n).map(|_| rand_canonical(rng)).collect();
                let value = self.comp.eval(&inputs);
                let mut buf = inputs;
                buf.push(value); // exp
                buf.push(0); // sel: else branch runs
                buf
            }
            GadgetKind::CompoundAssign => {
                let (a, b, c) = (rand_canonical(rng), rand_canonical(rng), rand_canonical(rng));
                let exp = mul_mod(add_mod(a, b), c);
                vec![a, b, c, exp]
            }
            GadgetKind::Div => {
                let a = rand_canonical(rng);
                let b = rand_canonical_nonzero(rng);
                vec![a, b, div_canonical(a, b)]
            }
            GadgetKind::MultiReturn => {
                let x = rand_canonical(rng);
                vec![x, add_mod(x, 1), add_mod(x, 2)]
            }
            GadgetKind::PointerOffset => {
                let fillers: Vec<u64> = (0..8).map(|_| rand_canonical(rng)).collect();
                let exp = fillers[3]; // arr[base(=0) + 3] == fillers[3]
                let mut buf = vec![0]; // base
                buf.extend(fillers);
                buf.push(exp);
                buf
            }
            GadgetKind::PointerOffsetSub => {
                let fillers: Vec<u64> = (0..8).map(|_| rand_canonical(rng)).collect();
                let exp = fillers[3]; // arr[base(=5) - 2] == arr[3] == fillers[3]
                let mut buf = vec![5]; // non-zero runtime base
                buf.extend(fillers);
                buf.push(exp);
                buf
            }
            GadgetKind::ParallelLoop { n } => {
                let v: Vec<u64> = (0..*n).map(|_| rand_canonical(rng)).collect();
                let mut buf = v.clone();
                buf.extend(v); // expected == value
                buf
            }
            GadgetKind::ConstFold { value, .. } => vec![*value],
            GadgetKind::ForwardDeclEq => {
                let (a, b) = (rand_canonical(rng), rand_canonical(rng));
                vec![a, b, 1, a] // sel = 1 ⇒ x = a; exp = a
            }
        }
    }

    /// A buffer that makes *only* the `k`-th check of this gadget fail, derived from an honest
    /// buffer. `k` must be in `0..self.n_violations()` (single-check gadgets ignore it).
    #[must_use]
    pub fn violating_buffer(&self, honest: &[u64], k: usize) -> Vec<u64> {
        debug_assert!(k < self.n_violations());
        let mut buf = honest.to_vec();
        let n = self.comp.n_inputs;
        match &self.kind {
            // Perturb the dedicated "expected" cell so only the target equality fails.
            GadgetKind::EqBound
            | GadgetKind::EqConst { .. }
            | GadgetKind::InlineWrapped
            | GadgetKind::IfThen
            | GadgetKind::IfElse
            | GadgetKind::Loop => {
                buf[n] = add_mod(buf[n], 1);
            }
            GadgetKind::MatchDispatch { .. } | GadgetKind::HintDiv { .. } | GadgetKind::MatchChained => {
                buf[1] = add_mod(buf[1], 1);
            }
            GadgetKind::TwoReadsEq => {
                // k=0 breaks the `w` side, k=1 the `v` side: `assert v == w` must reject either.
                buf[1 - k] = add_mod(buf[1 - k], 1);
            }
            GadgetKind::CopyPropEq => {
                buf[1] = add_mod(buf[1], 1); // exp no longer equals v
            }
            GadgetKind::Div => buf[2] = add_mod(buf[2], 1), // exp no longer equals a / b
            GadgetKind::CompoundAssign => buf[3] = add_mod(buf[3], 1),
            GadgetKind::ConstFold { .. } => buf[0] = add_mod(buf[0], 1),
            GadgetKind::PointerOffset | GadgetKind::PointerOffsetSub => buf[9] = add_mod(buf[9], 1),
            GadgetKind::MultiReturn => buf[1 + k] = add_mod(buf[1 + k], 1), // k=0 → e1, k=1 → e2
            GadgetKind::CseEq => {
                // k∈{0,1}: perturb the dedicated expected cell (exp1/exp2). k∈{2,3}: perturb a
                // shared *input* (in0/in1) — both products change, so the correct compiler rejects;
                // an accept means a check was bound to the wrong operand or read a stale value.
                match k {
                    0 | 1 => buf[2 + k] = add_mod(buf[2 + k], 1),
                    _ => buf[k - 2] = add_mod(buf[k - 2], 1),
                }
            }
            GadgetKind::RunningChain { len } => {
                if k < *len {
                    buf[len + k] = add_mod(buf[len + k], 1); // break only checkpoint k
                } else {
                    buf[0] = add_mod(buf[0], 1); // input-side: perturb the base ⇒ every checkpoint shifts
                }
            }
            GadgetKind::ExtOp { mode, n, .. } => {
                let off = ext_a_len(*mode, *n) + n * DIMENSION;
                buf[off + k] = add_mod(buf[off + k], 1); // perturb expected coord k
            }
            GadgetKind::Poseidon => {
                buf[16 + k] = add_mod(buf[16 + k], 1); // perturb expected output coord k
            }
            GadgetKind::NestedIfLoop { n } | GadgetKind::ParallelLoop { n } => {
                buf[n + k] = add_mod(buf[n + k], 1); // perturb expected of pair k
            }
            GadgetKind::NestedMutLoop { .. } => {
                buf[4 + k] = add_mod(buf[4 + k], 1); // k=0 → exp_a, k=1 → exp_b
            }
            GadgetKind::BitDecomp { n } => {
                if k < *n {
                    buf[k] = 2; // non-boolean ⇒ boolean assert k fails…
                    // …but keep the reconstruction satisfied so *only* boolean k is violated.
                    buf[*n] = buf[..*n].iter().fold(0u64, |a, &b| add_mod(mul_mod(a, 2), b));
                } else {
                    buf[*n] = add_mod(buf[*n], 1); // break the reconstruction only
                }
            }
            GadgetKind::Ne => {
                buf[n] = self.comp.eval(&honest[..n]); // other := value ⇒ `!=` fails
            }
            GadgetKind::Bool => {
                buf[0] = 2 + rand_canonical_nonzero(&mut Rng::new(self.id as u64)) % (P - 2);
            }
            GadgetKind::Panic => buf[0] = 1, // take the branch ⇒ assert False fires
            GadgetKind::DebugAssertLt { bound } => buf[0] = *bound, // value == bound ⇒ `value < bound` false
            GadgetKind::ForwardDeclEq => buf[3] = add_mod(buf[3], 1), // exp no longer equals x
            GadgetKind::RangeLt { bound } => buf[0] = *bound,
            GadgetKind::RangeLe { bound } => buf[0] = *bound + 1,
            GadgetKind::UnrolledRangeLt { bound, .. } => buf[k] = *bound, // iteration k out of range
        }
        buf
    }
}
