//! Semantics-preserving program transforms (metamorphic testing).
//!
//! Each transform rewrites a [`CheckedProgram`] into a structurally different but semantically
//! equivalent one: the same set of checks must still be enforced. Because gadgets are
//! independent, reordering or duplicating them cannot change any verdict — so if a transformed
//! variant drops a check (or rejects an honest witness) while the base does not, the compiler
//! has an order/duplication-dependent miscompilation. The variants also reach program shapes
//! the random generator alone rarely produces (e.g. two structurally identical checks adjacent,
//! which stresses CSE / assert fusion).
//!
//! Variants are evaluated by the same [`crate::oracles`], so any dropped check surfaces exactly
//! as in the base case; the reproducer's source identifies the transformed program.

use crate::model::{CheckedProgram, Gadget};
use crate::rng::Rng;

/// Reassign gadget ids to their position (ids drive variable prefixes and buffer order).
fn reindex(mut gadgets: Vec<Gadget>) -> CheckedProgram {
    for (i, g) in gadgets.iter_mut().enumerate() {
        g.id = i;
    }
    CheckedProgram::new(gadgets)
}

/// Randomly permute the gadgets. Independent gadgets must behave identically in any order.
#[must_use]
pub fn reorder(prog: &CheckedProgram, rng: &mut Rng) -> CheckedProgram {
    let mut gadgets = prog.gadgets.clone();
    rng.shuffle(&mut gadgets);
    reindex(gadgets)
}

/// Emit every gadget twice (with fresh buffers). Both copies of each check must be enforced;
/// adjacent identical-shaped checks stress CSE / assert fusion.
#[must_use]
pub fn duplicate(prog: &CheckedProgram) -> CheckedProgram {
    let mut gadgets = Vec::with_capacity(prog.gadgets.len() * 2);
    for g in &prog.gadgets {
        gadgets.push(g.clone());
        gadgets.push(g.clone());
    }
    reindex(gadgets)
}
