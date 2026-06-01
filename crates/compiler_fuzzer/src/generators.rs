//! Random, seed-deterministic generation of [`CheckedProgram`]s.
//!
//! A program is a sequence of gadgets; each gadget is a random kind plus (for the
//! equality/inequality kinds) a random straight-line [`Computation`]. Computations stay in a
//! "nice" subset (no division, modest constants) so the *honest* witness always exists and the
//! reference interpreter stays exact — the point is to stress the compiler's lowering and
//! simplification of *checks*, not to exercise field pathologies (those have dedicated
//! generators).

use crate::field_util::{
    ExtMode, ExtOp, add_mod, div_ceil_int, div_floor_int, log2_ceil_int, mul_mod, next_multiple_int, pow_mod, sub_mod,
};
use crate::model::{CheckedProgram, Computation, Gadget, GadgetKind, Op, Operand, Step};
use crate::rng::Rng;

/// Knobs controlling program shape. All bounds are inclusive.
#[derive(Debug, Clone)]
pub struct GenConfig {
    pub min_gadgets: usize,
    pub max_gadgets: usize,
    /// Max inputs a computation reads.
    pub max_inputs: usize,
    /// Max straight-line steps in a computation.
    pub max_steps: usize,
    /// Probability (in percent) that a computation operand is a small constant.
    pub const_percent: u32,
    /// Largest constant emitted as `assert value == C` (kept well below the field modulus and
    /// `i32::MAX` so this generator never trips parser-overflow edges — those are probed
    /// separately).
    pub max_eq_const: u64,
    /// Largest constant used as a computation operand.
    pub max_step_const: u64,
}

impl Default for GenConfig {
    fn default() -> Self {
        Self {
            min_gadgets: 1,
            max_gadgets: 8,
            max_inputs: 4,
            max_steps: 6,
            const_percent: 25,
            max_eq_const: 1 << 30,
            max_step_const: 1 << 20,
        }
    }
}

/// Generate a complete program.
#[must_use]
pub fn gen_program(rng: &mut Rng, cfg: &GenConfig) -> CheckedProgram {
    let n = rng.range(cfg.min_gadgets, cfg.max_gadgets);
    let gadgets = (0..n).map(|id| gen_gadget(rng, cfg, id)).collect();
    CheckedProgram::new(gadgets)
}

/// Generate a single gadget with a given id, spanning all kinds (and thus all of the compiler's
/// harder lowering paths).
#[must_use]
pub fn gen_gadget(rng: &mut Rng, cfg: &GenConfig, id: usize) -> Gadget {
    let range_bound = |rng: &mut Rng| {
        // The deref-based range check is sound for bound <= 2^16. Occasionally probe exactly that
        // boundary (2^16 and 2^16-1) — where an off-by-one in the `bound-1-value` deref would bite —
        // since the generic path below never reaches it (RANGE_MAX = 2^16 - 2).
        if rng.chance(1, 12) {
            *rng.choice(&[(1u64 << 16) - 1, 1u64 << 16])
        } else {
            2 + rng.next_u64() % (crate::model::RANGE_MAX - 1)
        }
    };
    // A loop length kept small so range→recursion stays cheap.
    let loop_len = |rng: &mut Rng| Computation::identity(rng.range(1, 4));
    let ext_op = |rng: &mut Rng| {
        let op = *rng.choice(&[ExtOp::Add, ExtOp::Dot, ExtOp::PolyEq]);
        let mode = *rng.choice(&[ExtMode::Ee, ExtMode::Be]);
        GadgetKind::ExtOp {
            op,
            mode,
            // Cover odd lengths (3, 5, 7) and larger n, where the extension-op AIR's *backward*
            // accumulation and BE/EE stride are most likely to surface an off-by-one — not just the
            // n ∈ {1, 2} the suite previously generated.
            n: rng.range(1, 8),
        }
    };

    let (kind, comp) = match rng.below(35) {
        0 => (GadgetKind::EqBound, gen_computation(rng, cfg)),
        1 => (
            GadgetKind::EqConst {
                c: rng.next_u64() % cfg.max_eq_const,
            },
            gen_computation(rng, cfg),
        ),
        2 => (GadgetKind::Ne, gen_computation(rng, cfg)),
        3 => (GadgetKind::Bool, Computation::identity(1)),
        4 => (
            GadgetKind::RangeLt {
                bound: range_bound(rng),
            },
            Computation::identity(1),
        ),
        5 => (
            GadgetKind::RangeLe {
                // `x <= B` lowers to `x < B + 1`, so the max *sound* bound for `<=` is 2^16 - 1
                // (not 2^16, which the `<` checks may use). Clamp so the boundary case stays valid.
                bound: range_bound(rng).min((1 << 16) - 1),
            },
            Computation::identity(1),
        ),
        6 => (GadgetKind::IfThen, gen_computation(rng, cfg)),
        7 => (GadgetKind::Loop, loop_len(rng)),
        8 => (
            GadgetKind::MatchDispatch {
                m: rng.range(2, 8) as u64,
            },
            Computation::identity(1),
        ),
        9 => (GadgetKind::InlineWrapped, gen_computation(rng, cfg)),
        10 => (
            GadgetKind::HintDiv {
                d: rng.range(2, 64) as u64,
            },
            Computation::identity(1),
        ),
        // Passes most likely to silently drop a check: copy-propagation, CSE, assert-fusion.
        11 => (GadgetKind::CopyPropEq, Computation::identity(1)),
        12 => (GadgetKind::CseEq, Computation::identity(1)),
        13 => (GadgetKind::TwoReadsEq, Computation::identity(1)),
        14 => (
            GadgetKind::RunningChain { len: rng.range(2, 6) },
            Computation::identity(1),
        ),
        15 => (ext_op(rng), Computation::identity(1)),
        16 => (
            GadgetKind::NestedIfLoop { n: rng.range(2, 5) },
            Computation::identity(1),
        ),
        // The canonical hint-then-constrain decomposition (boolean + reconstruction).
        17 => (GadgetKind::BitDecomp { n: rng.range(2, 12) }, Computation::identity(1)),
        18 => (GadgetKind::Panic, Computation::identity(1)),
        19 => (
            GadgetKind::DebugAssertLt {
                bound: range_bound(rng),
            },
            Computation::identity(1),
        ),
        20 => (GadgetKind::IfElse, gen_computation(rng, cfg)),
        21 => (GadgetKind::CompoundAssign, Computation::identity(1)),
        22 => (GadgetKind::Div, Computation::identity(1)),
        23 => (GadgetKind::MultiReturn, Computation::identity(1)),
        24 => (GadgetKind::PointerOffset, Computation::identity(1)),
        25 => (
            GadgetKind::ParallelLoop { n: rng.range(2, 5) },
            Computation::identity(1),
        ),
        26 => (GadgetKind::ForwardDeclEq, Computation::identity(1)),
        27 => (
            GadgetKind::NestedMutLoop {
                outer: rng.range(1, 4),
                inner: rng.range(1, 3),
            },
            Computation::identity(1),
        ),
        28 => (
            GadgetKind::UnrolledRangeLt {
                n: rng.range(2, 6),
                bound: range_bound(rng),
            },
            Computation::identity(1),
        ),
        29 => (GadgetKind::PointerOffsetSub, Computation::identity(1)),
        30 => (GadgetKind::MatchChained, Computation::identity(1)),
        31 => (GadgetKind::Poseidon, Computation::identity(1)),
        32 => (GadgetKind::IfElseBoth, Computation::identity(1)),
        33 => (
            GadgetKind::LoopFormsAgree { n: rng.range(2, 6) },
            Computation::identity(1),
        ),
        _ => {
            let (src, value) = gen_const_fold(rng);
            (GadgetKind::ConstFold { src, value }, Computation::identity(1))
        }
    };
    Gadget { id, kind, comp }
}

/// Generate a compile-time constant expression mixing every const built-in, paired with an
/// *independent* reference value (computed here, never via the compiler). The emitted expression
/// is fully parenthesized so its left-to-right evaluation matches the fold below regardless of the
/// parser's precedence. A miscompiled constant fold makes `assert v == <expr>` reject the honest
/// witness (`v == reference`).
#[must_use]
pub fn gen_const_fold(rng: &mut Rng) -> (String, u64) {
    // A single term: (source, reference value in [0, P)).
    fn term(rng: &mut Rng) -> (String, u64) {
        match rng.below(7) {
            0 => {
                let base = 2 + rng.below(2) as u64; // 2 or 3
                let exp = rng.range(1, 30) as u64;
                (format!("{base} ** {exp}"), pow_mod(base, exp))
            }
            1 => {
                let a = rng.next_u64() % 100_000;
                let b = 1 + rng.next_u64() % 1000;
                (format!("div_floor({a}, {b})"), div_floor_int(a, b))
            }
            2 => {
                let a = rng.next_u64() % 100_000;
                let b = 1 + rng.next_u64() % 1000;
                (format!("div_ceil({a}, {b})"), div_ceil_int(a, b))
            }
            3 => {
                let a = rng.next_u64() % 100_000;
                let b = rng.next_u64() % 100_000;
                (format!("saturating_sub({a}, {b})"), a.saturating_sub(b))
            }
            4 => {
                let a = rng.next_u64() % 10_000;
                let b = 1 + rng.next_u64() % 1000;
                (format!("next_multiple_of({a}, {b})"), next_multiple_int(a, b))
            }
            5 => {
                let a = 2 + rng.next_u64() % 65_534;
                (format!("log2_ceil({a})"), log2_ceil_int(a))
            }
            _ => {
                let a = rng.next_u64() % 100_000;
                let b = 1 + rng.next_u64() % 1000;
                (format!("{a} % {b}"), a % b)
            }
        }
    }

    let (mut src, mut val) = term(rng);
    src = format!("({src})");
    let n_more = rng.range(1, 3);
    for _ in 0..n_more {
        let (ts, tv) = term(rng);
        let (sym, nv) = match rng.below(3) {
            0 => ("+", add_mod(val, tv)),
            1 => ("-", sub_mod(val, tv)),
            _ => ("*", mul_mod(val, tv)),
        };
        src = format!("({src} {sym} ({ts}))");
        val = nv;
    }
    (src, val)
}

/// Generate a random straight-line computation with at least one input.
#[must_use]
pub fn gen_computation(rng: &mut Rng, cfg: &GenConfig) -> Computation {
    let n_inputs = rng.range(1, cfg.max_inputs.max(1));
    let n_steps = rng.below(cfg.max_steps + 1);
    let mut steps = Vec::with_capacity(n_steps);
    for i in 0..n_steps {
        let op = *rng.choice(&[Op::Add, Op::Sub, Op::Mul]);
        let a = gen_operand(rng, cfg, n_inputs, i);
        let b = gen_operand(rng, cfg, n_inputs, i);
        steps.push(Step { op, a, b });
    }
    Computation { n_inputs, steps }
}

/// A random operand referring only to already-defined values (inputs, earlier temps) or a
/// small constant.
fn gen_operand(rng: &mut Rng, cfg: &GenConfig, n_inputs: usize, n_temps: usize) -> Operand {
    if rng.chance(cfg.const_percent, 100) {
        return Operand::Const(rng.next_u64() % cfg.max_step_const.max(1));
    }
    // Choose uniformly across the available inputs and earlier temps.
    let pool = n_inputs + n_temps;
    let pick = rng.below(pool);
    if pick < n_inputs {
        Operand::Input(pick)
    } else {
        Operand::Temp(pick - n_inputs)
    }
}
