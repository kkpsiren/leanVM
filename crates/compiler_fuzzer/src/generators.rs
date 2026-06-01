//! Random, seed-deterministic generation of [`CheckedProgram`]s.
//!
//! A program is a sequence of gadgets; each gadget is a random kind plus (for the
//! equality/inequality kinds) a random straight-line [`Computation`]. Computations stay in a
//! "nice" subset (no division, modest constants) so the *honest* witness always exists and the
//! reference interpreter stays exact — the point is to stress the compiler's lowering and
//! simplification of *checks*, not to exercise field pathologies (those have dedicated
//! generators).

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
    let range_bound = |rng: &mut Rng| 2 + rng.next_u64() % (crate::model::RANGE_MAX - 1);
    // A loop length kept small so range→recursion stays cheap.
    let loop_len = |rng: &mut Rng| Computation::identity(rng.range(1, 4));

    let (kind, comp) = match rng.below(18) {
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
                bound: range_bound(rng),
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
        15 => (GadgetKind::ExtMulEq, Computation::identity(1)),
        _ => (
            GadgetKind::NestedIfLoop { n: rng.range(2, 5) },
            Computation::identity(1),
        ),
    };
    Gadget { id, kind, comp }
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
