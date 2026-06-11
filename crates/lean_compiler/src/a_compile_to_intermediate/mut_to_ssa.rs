//! Mutable-variable elimination (SSA-style renaming) at the AST level.
//!
//! Every mutable `x` becomes a sequence of immutable versions `__mut_x_0,
//! __mut_x_1, ...`: `x: Mut = e` assigns `__mut_x_0`, each reassignment
//! introduces the next version, reads use the current one. When `if`/`match`
//! branches end at different versions they are unified (see
//! [`unify_branch_versions`]). `range` loops cannot reassign enclosing mutables
//! (rejected earlier), so a loop body only ever reads outer versions.

use crate::{ast_passes::*, lang::*};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn eliminate_mutables(program: &mut Program) {
    for func in program.functions.values_mut() {
        let mut tracker = SsaTracker::default();
        func.body = ssa_block(std::mem::take(&mut func.body), &mut tracker);
    }
}

#[derive(Debug, Clone, Default)]
struct SsaTracker {
    /// mutable variable -> current version
    versions: BTreeMap<Var, usize>,
}

impl SsaTracker {
    fn versioned_name(var: &Var, version: usize) -> Var {
        format!("__mut_{var}_{version}")
    }

    fn current_name(&self, var: &Var) -> Var {
        match self.versions.get(var) {
            Some(version) => Self::versioned_name(var, *version),
            None => var.clone(),
        }
    }

    /// Renames reads of tracked variables to their current version.
    fn rename_reads(&self, var: &Var) -> VarTransform {
        match self.versions.get(var) {
            Some(version) => VarTransform::Rename(Self::versioned_name(var, *version)),
            None => VarTransform::Keep,
        }
    }

    fn register(&mut self, var: &Var) {
        self.versions.insert(var.clone(), 0);
    }

    fn increment(&mut self, var: &Var) -> Var {
        let version = self.versions.get_mut(var).unwrap();
        *version += 1;
        Self::versioned_name(var, *version)
    }
}

/// The (immutable) name to assign for a `Var` target, updating the tracker:
/// `: Mut` registers, a reassignment of a tracked var bumps its version.
fn process_var_target(tracker: &mut SsaTracker, var: &Var, is_mutable: bool) -> Var {
    if is_mutable {
        tracker.register(var);
        tracker.current_name(var)
    } else if tracker.versions.contains_key(var) {
        tracker.increment(var)
    } else {
        var.clone()
    }
}

fn ssa_block(lines: Vec<Line>, tracker: &mut SsaTracker) -> Vec<Line> {
    let mut out = Vec::with_capacity(lines.len());
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, is_mutable } => {
                if is_mutable {
                    tracker.register(&var);
                    out.push(Line::ForwardDeclaration {
                        var: tracker.current_name(&var),
                        is_mutable: false,
                    });
                } else {
                    out.push(Line::ForwardDeclaration { var, is_mutable });
                }
            }
            Line::Statement {
                mut targets,
                mut value,
                location,
            } => {
                // RHS reads use pre-bump versions; variable targets bump next;
                // array-access targets then resolve against post-bump versions.
                transform_vars_in_expr(&mut value, &|v| tracker.rename_reads(v));
                for target in &mut targets {
                    if let AssignmentTarget::Var { var, is_mutable } = target {
                        *target = AssignmentTarget::Var {
                            var: process_var_target(tracker, var, *is_mutable),
                            is_mutable: false,
                        };
                    }
                }
                for target in &mut targets {
                    if let AssignmentTarget::ArrayAccess { array, index } = target {
                        transform_vars_in_simple_expr(array, &|v| tracker.rename_reads(v));
                        transform_vars_in_expr(index, &|v| tracker.rename_reads(v));
                    }
                }
                out.push(Line::Statement {
                    targets,
                    value,
                    location,
                });
            }
            Line::Assert {
                debug,
                mut boolean,
                location,
            } => {
                transform_vars_in_expr(&mut boolean.left, &|v| tracker.rename_reads(v));
                transform_vars_in_expr(&mut boolean.right, &|v| tracker.rename_reads(v));
                out.push(Line::Assert {
                    debug,
                    boolean,
                    location,
                });
            }
            Line::IfCondition {
                mut condition,
                then_branch,
                else_branch,
                location,
            } => {
                transform_vars_in_expr(&mut condition.left, &|v| tracker.rename_reads(v));
                transform_vars_in_expr(&mut condition.right, &|v| tracker.rename_reads(v));

                let snapshot = tracker.clone();
                let mut then_tracker = snapshot.clone();
                let then_simplified = ssa_block(then_branch, &mut then_tracker);
                let mut else_tracker = snapshot;
                let else_simplified = ssa_block(else_branch, &mut else_tracker);

                let mut branches = [then_simplified, else_simplified];
                let branch_versions = [then_tracker.versions, else_tracker.versions];
                let decls = unify_branch_versions(tracker, &branch_versions, &mut branches, location);
                out.extend(decls);

                let [then_branch, else_branch] = branches;
                out.push(Line::IfCondition {
                    condition,
                    then_branch,
                    else_branch,
                    location,
                });
            }
            Line::Match {
                mut value,
                arms,
                location,
            } => {
                transform_vars_in_expr(&mut value, &|v| tracker.rename_reads(v));

                let snapshot = tracker.clone();
                let mut branches = Vec::with_capacity(arms.len());
                let mut branch_versions = Vec::with_capacity(arms.len());
                let mut patterns = Vec::with_capacity(arms.len());
                for (pattern, arm) in arms {
                    let mut arm_tracker = snapshot.clone();
                    branches.push(ssa_block(arm, &mut arm_tracker));
                    branch_versions.push(arm_tracker.versions);
                    patterns.push(pattern);
                }

                let decls = unify_branch_versions(tracker, &branch_versions, &mut branches, location);
                out.extend(decls);

                out.push(Line::Match {
                    value,
                    arms: patterns.into_iter().zip(branches).collect(),
                    location,
                });
            }
            Line::ForLoop {
                iterator,
                mut start,
                mut end,
                body,
                loop_kind,
                location,
            } => {
                assert!(
                    !loop_kind.is_unroll(),
                    "unroll loops should have been expanded before SSA"
                );
                transform_vars_in_expr(&mut start, &|v| tracker.rename_reads(v));
                transform_vars_in_expr(&mut end, &|v| tracker.rename_reads(v));

                // The body reads outer mutables but cannot reassign them, so any
                // version change inside is body-local: drop it.
                let mut body_tracker = tracker.clone();
                body_tracker.versions.remove(&iterator); // the iterator shadows any outer name
                let body = ssa_block(body, &mut body_tracker);

                out.push(Line::ForLoop {
                    iterator,
                    start,
                    end,
                    body,
                    loop_kind,
                    location,
                });
            }
            Line::FunctionRet { mut return_data } => {
                for expr in &mut return_data {
                    transform_vars_in_expr(expr, &|v| tracker.rename_reads(v));
                }
                out.push(Line::FunctionRet { return_data });
            }
            Line::Panic { .. } | Line::LocationReport { .. } => out.push(line),
        }
    }
    out
}

/// Unifies mutable versions across the branches of an `if` / `match`. On entry
/// `tracker` holds the pre-branch versions; on exit, the unified ones. Only
/// variables tracked before the construct can outlive it. Per such variable:
/// early-exiting (return/panic) branches are ignored; if every continuing
/// branch ends at the same version it becomes current; otherwise a fresh
/// unified version is forward-declared before the construct and assigned at the
/// end of each continuing branch.
fn unify_branch_versions(
    tracker: &mut SsaTracker,
    branch_versions: &[BTreeMap<Var, usize>],
    branches: &mut [Vec<Line>],
    location: SourceLocation,
) -> Vec<Line> {
    let mut forward_decls = Vec::new();
    let branch_exits_early: Vec<bool> = branches.iter().map(|b| ends_with_early_exit(b)).collect();
    let snapshot_versions = tracker.versions.clone();
    // Declarations hoisted before the construct; their nested copies inside the
    // branches must be removed (the hoisted one would shadow them).
    let mut decls_to_remove = BTreeSet::new();

    for (var, &snapshot_version) in &snapshot_versions {
        let continuing_versions: Vec<usize> = branch_versions
            .iter()
            .zip(&branch_exits_early)
            .filter(|(_, exits)| !**exits)
            .map(|(versions, _)| versions.get(var).copied().unwrap_or(snapshot_version))
            .collect();

        // All branches exit early: keep the snapshot version.
        let Some(&first_version) = continuing_versions.first() else {
            continue;
        };

        if continuing_versions.iter().all(|&v| v == first_version) {
            // Continuing branches agree; hoist a declaration if the version was
            // created inside the branches.
            if first_version > snapshot_version {
                let versioned_var = SsaTracker::versioned_name(var, first_version);
                forward_decls.push(Line::ForwardDeclaration {
                    var: versioned_var.clone(),
                    is_mutable: false,
                });
                decls_to_remove.insert(versioned_var);
            }
            tracker.versions.insert(var.clone(), first_version);
        } else {
            // Versions differ: introduce a unified one. The +1 is over *all*
            // branches (even early-exiting) so the unified name can't collide
            // with a version declared inside any branch.
            let all_versions_max = branch_versions
                .iter()
                .map(|versions| versions.get(var).copied().unwrap_or(snapshot_version))
                .max()
                .unwrap();
            let unified_version = all_versions_max + 1;
            let unified_name = SsaTracker::versioned_name(var, unified_version);
            forward_decls.push(Line::ForwardDeclaration {
                var: unified_name.clone(),
                is_mutable: false,
            });

            for (branch_idx, versions) in branch_versions.iter().enumerate() {
                if branch_exits_early[branch_idx] {
                    continue;
                }
                let branch_version = versions.get(var).copied().unwrap_or(snapshot_version);
                branches[branch_idx].push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: unified_name.clone(),
                        is_mutable: false,
                    }],
                    value: Expression::var(SsaTracker::versioned_name(var, branch_version)),
                    location,
                });
            }

            tracker.versions.insert(var.clone(), unified_version);
        }
    }

    if !decls_to_remove.is_empty() {
        for branch in branches.iter_mut() {
            remove_forward_declarations(branch, &decls_to_remove);
        }
    }

    forward_decls
}

fn remove_forward_declarations(lines: &mut Vec<Line>, vars: &BTreeSet<Var>) {
    lines.retain_mut(|line| {
        if let Line::ForwardDeclaration { var, .. } = line
            && vars.contains(var)
        {
            return false;
        }
        for block in line.nested_blocks_mut() {
            remove_forward_declarations(block, vars);
        }
        true
    });
}
