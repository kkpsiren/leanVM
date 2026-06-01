//! Mutable-variable SSA pass (runs over the high-level `Line` AST).
//!
//! The zkVM has write-once memory, so every variable must be assigned exactly
//! once. Source programs, however, allow mutable variables (`x: Mut`) that are
//! reassigned. This pass rewrites each mutable variable into a sequence of
//! distinct single-assignment versions `@mut_x_0`, `@mut_x_1`, … — one per
//! assignment — and rewrites each read to refer to the version in effect at that
//! point. After this pass the program contains no mutable variables, so the
//! later lowering (`simplify_lines`) never has to think about versioning.
//!
//! The only subtlety is control flow: when a variable is reassigned inside some
//! branches of an `if`/`match`, the code after the branch must see ONE version
//! regardless of which branch ran. [`unify_branch_versions`] reconciles the
//! per-branch versions, inserting a forward-declaration before the branch (so the
//! merged version is allocated in the enclosing scope) and, when branches end on
//! different versions, a copy `@mut_x_merged = @mut_x_branch` at the end of each
//! branch — i.e. classic SSA phi nodes, expressed as ordinary copies.

use std::collections::{BTreeMap, BTreeSet};

use lean_vm::BooleanExpr;

use super::VarOrConstMallocAccess;
use crate::lang::{AssignmentTarget, Expression, Function, Line, Program, SimpleExpr, SourceLocation, Var};

/// Rewrite every mutable variable in the program into SSA versions.
pub(super) fn resolve_mutable_vars(program: &mut Program) -> Result<(), String> {
    for func in program.functions.values_mut() {
        rewrite_function(func)?;
    }
    Ok(())
}

fn rewrite_function(func: &mut Function) -> Result<(), String> {
    let mut tracker = Tracker::default();
    // Arguments are immutable and already bound on entry.
    for arg in &func.arguments {
        tracker.assigned.insert(arg.name.clone());
    }
    func.body = ssa_lines(&func.body, &mut tracker)?;
    Ok(())
}

/// Tracks, while walking a block, the current version of each mutable variable
/// and which immutable variables have already been assigned.
#[derive(Debug, Clone, Default)]
struct Tracker {
    /// mutable variable name → current version number (0 = first assignment).
    versions: BTreeMap<Var, usize>,
    /// immutable variables already assigned, to reject double assignment.
    assigned: BTreeSet<Var>,
}

impl Tracker {
    fn is_mutable(&self, var: &Var) -> bool {
        self.versions.contains_key(var)
    }

    /// The name a read of `var` should resolve to right now (unchanged if `var`
    /// is not a mutable variable).
    fn current_name(&self, var: &Var) -> Var {
        match self.versions.get(var) {
            Some(version) => format!("@mut_{var}_{version}"),
            None => var.clone(),
        }
    }

    /// Begin tracking `var` as mutable at version 0.
    fn register_mutable(&mut self, var: &Var) {
        self.versions.insert(var.clone(), 0);
    }

    /// Bump `var` to its next version and return that versioned name.
    fn next_version(&mut self, var: &Var) -> Var {
        let version = self.versions.entry(var.clone()).or_insert(0);
        *version += 1;
        format!("@mut_{var}_{version}")
    }

    /// Reject reassignment of an immutable variable. Compiler-generated names
    /// (prefixed `@`) are exempt.
    fn check_immutable_assignment(&mut self, var: &Var) -> Result<(), String> {
        if var.starts_with('@') || self.assigned.insert(var.clone()) {
            Ok(())
        } else {
            Err(format!(
                "Cannot reassign immutable variable '{var}'. Use '{var}: Mut' for mutable variables, or 'assert {var} == <value>;' to check equality"
            ))
        }
    }
}

/// SSA-rewrite a block, returning the new lines (with inserted forward-decls and
/// phi copies). Mutates `tracker` to reflect the versions live at the block's end.
fn ssa_lines(lines: &[Line], tracker: &mut Tracker) -> Result<Vec<Line>, String> {
    let mut out = Vec::new();
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, is_mutable } => {
                if *is_mutable {
                    tracker.register_mutable(var);
                }
                out.push(Line::ForwardDeclaration {
                    var: tracker.current_name(var),
                    is_mutable: false,
                });
            }
            Line::Statement {
                targets,
                value,
                location,
            } => out.push(ssa_statement(targets, value, *location, tracker)?),
            Line::Assert {
                boolean,
                debug,
                location,
            } => {
                let mut boolean = boolean.clone();
                rename_reads(&mut boolean.left, tracker);
                rename_reads(&mut boolean.right, tracker);
                out.push(Line::Assert {
                    boolean,
                    debug: *debug,
                    location: *location,
                });
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                location,
            } => ssa_if(&mut out, condition, then_branch, else_branch, *location, tracker)?,
            Line::Match { value, arms, location } => ssa_match(&mut out, value, arms, *location, tracker)?,
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                loop_kind,
                location,
            } => {
                let mut start = start.clone();
                let mut end = end.clone();
                rename_reads(&mut start, tracker);
                rename_reads(&mut end, tracker);
                // The loop body becomes its own function, so immutable assignments
                // inside it don't collide with names outside. Mutable versions
                // persist: a non-unrolled loop never reassigns an external mutable
                // (those were turned into buffer arrays by an earlier pass), so the
                // only reassignments here are to body-local mutables.
                let saved_assigned = std::mem::take(&mut tracker.assigned);
                let body = ssa_lines(body, tracker)?;
                tracker.assigned = saved_assigned;
                out.push(Line::ForLoop {
                    iterator: iterator.clone(),
                    start,
                    end,
                    body,
                    loop_kind: loop_kind.clone(),
                    location: *location,
                });
            }
            Line::FunctionRet { return_data } => {
                let mut return_data = return_data.clone();
                for expr in &mut return_data {
                    rename_reads(expr, tracker);
                }
                out.push(Line::FunctionRet { return_data });
            }
            Line::Panic { .. } | Line::LocationReport { .. } => out.push(line.clone()),
        }
    }
    Ok(out)
}

/// SSA-rewrite a single assignment: rename the reads on the right-hand side (and
/// in any array-index targets) BEFORE choosing fresh names for the targets, so a
/// self-referential assignment like `x = x + 1` reads the old version.
fn ssa_statement(
    targets: &[AssignmentTarget],
    value: &Expression,
    location: SourceLocation,
    tracker: &mut Tracker,
) -> Result<Line, String> {
    let mut value = value.clone();
    rename_reads(&mut value, tracker);

    let mut targets = targets.to_vec();
    // Reads in an array-element target (the base pointer and the index) use the
    // current versions, just like the right-hand side.
    for target in &mut targets {
        if let AssignmentTarget::ArrayAccess { array, index } = target {
            rename_simple_read(array, tracker);
            rename_reads(index, tracker);
        }
    }
    // Now version the variable targets.
    for target in &mut targets {
        if let AssignmentTarget::Var { var, is_mutable } = target {
            *var = if *is_mutable {
                tracker.register_mutable(var);
                tracker.current_name(var)
            } else if tracker.is_mutable(var) {
                tracker.next_version(var)
            } else {
                tracker.check_immutable_assignment(var)?;
                var.clone()
            };
            *is_mutable = false;
        }
    }

    Ok(Line::Statement {
        targets,
        value,
        location,
    })
}

fn ssa_if(
    out: &mut Vec<Line>,
    condition: &BooleanExpr<Expression>,
    then_branch: &[Line],
    else_branch: &[Line],
    location: SourceLocation,
    tracker: &mut Tracker,
) -> Result<(), String> {
    let mut condition = condition.clone();
    rename_reads(&mut condition.left, tracker);
    rename_reads(&mut condition.right, tracker);

    let snapshot = tracker.versions.clone();
    let (then_out, then_versions) = ssa_branch(then_branch, &snapshot, tracker)?;
    let (else_out, else_versions) = ssa_branch(else_branch, &snapshot, tracker)?;

    let mut branches = [then_out, else_out];
    let forward_decls = unify_branch_versions(tracker, &snapshot, &[then_versions, else_versions], &mut branches);
    out.extend(forward_decls);
    let [then_branch, else_branch] = branches;
    out.push(Line::IfCondition {
        condition,
        then_branch,
        else_branch,
        location,
    });
    Ok(())
}

fn ssa_match(
    out: &mut Vec<Line>,
    value: &Expression,
    arms: &[(usize, Vec<Line>)],
    location: SourceLocation,
    tracker: &mut Tracker,
) -> Result<(), String> {
    let mut value = value.clone();
    rename_reads(&mut value, tracker);

    let snapshot = tracker.versions.clone();
    let mut patterns = Vec::new();
    let mut bodies = Vec::new();
    let mut arm_versions = Vec::new();
    for (pattern, body) in arms {
        let (body_out, versions) = ssa_branch(body, &snapshot, tracker)?;
        patterns.push(*pattern);
        bodies.push(body_out);
        arm_versions.push(versions);
    }

    let forward_decls = unify_branch_versions(tracker, &snapshot, &arm_versions, &mut bodies);
    out.extend(forward_decls);
    out.push(Line::Match {
        value,
        arms: patterns.into_iter().zip(bodies).collect(),
        location,
    });
    Ok(())
}

/// Process one branch starting from `snapshot` versions, returning its rewritten
/// lines and the versions live at its end. The branch uses a fresh `assigned`
/// set seeded from the outer one (each branch is a separate control-flow path).
fn ssa_branch(
    body: &[Line],
    snapshot: &BTreeMap<Var, usize>,
    tracker: &Tracker,
) -> Result<(Vec<Line>, BTreeMap<Var, usize>), String> {
    let mut branch_tracker = Tracker {
        versions: snapshot.clone(),
        assigned: tracker.assigned.clone(),
    };
    let lines = ssa_lines(body, &mut branch_tracker)?;
    Ok((lines, branch_tracker.versions))
}

/// Reconcile the per-branch versions of every mutable variable so that code after
/// the branch sees a single version. Returns forward-declarations to emit before
/// the branch; may append phi-copy assignments to the ends of `branches`. Updates
/// `tracker.versions` to the merged versions.
fn unify_branch_versions(
    tracker: &mut Tracker,
    snapshot: &BTreeMap<Var, usize>,
    branch_versions: &[BTreeMap<Var, usize>],
    branches: &mut [Vec<Line>],
) -> Vec<Line> {
    let mut forward_decls = Vec::new();
    let exits_early: Vec<bool> = branches.iter().map(|b| ends_with_early_exit(b)).collect();
    let mut branch_local = Vec::new();

    for var in tracker.versions.clone().keys() {
        let was_in_snapshot = snapshot.contains_key(var);
        let snapshot_v = snapshot.get(var).copied().unwrap_or(0);

        // Versions from branches that fall through (those that return/panic never
        // reach the code after the construct, so they don't constrain the merge).
        let continuing: Vec<(bool, usize)> = branch_versions
            .iter()
            .zip(&exits_early)
            .filter(|(_, exits)| !**exits)
            .map(|(v, _)| (v.contains_key(var), v.get(var).copied().unwrap_or(0)))
            .collect();

        if continuing.is_empty() {
            // Every branch exits early: keep the pre-branch version.
            tracker.versions.insert(var.clone(), snapshot_v);
            continue;
        }

        // A variable introduced inside only some branches is branch-local and dies
        // with them.
        if !was_in_snapshot && !continuing.iter().all(|(has, _)| *has) {
            branch_local.push(var.clone());
            continue;
        }

        let versions: Vec<usize> = continuing.iter().map(|(_, v)| *v).collect();
        if versions.iter().all(|&v| v == versions[0]) {
            // All continuing branches end on the same version.
            let merged = versions[0];
            if merged > snapshot_v {
                // It was (re)assigned identically in every branch; declare it in
                // the enclosing scope so it survives past the branch. If a nested
                // branch already declared this version inside itself, move that
                // declaration out here to avoid an inner declaration shadowing the
                // enclosing one (which would split it across two memory slots).
                let merged_var = versioned(var, merged);
                forward_decls.push(forward_decl(&merged_var));
                for branch in branches.iter_mut() {
                    remove_forward_declarations(branch, &merged_var);
                }
            }
            tracker.versions.insert(var.clone(), merged);
        } else {
            // Branches disagree: introduce a fresh merged version and copy each
            // branch's final version into it (a phi node, as ordinary copies).
            let merged = versions.iter().copied().max().unwrap() + 1;
            let merged_var = versioned(var, merged);
            forward_decls.push(forward_decl(&merged_var));
            for (branch_idx, branch_versions) in branch_versions.iter().enumerate() {
                if exits_early[branch_idx] {
                    continue;
                }
                let branch_v = branch_versions.get(var).copied().unwrap_or(0);
                branches[branch_idx].push(copy_var(&merged_var, &versioned(var, branch_v)));
            }
            tracker.versions.insert(var.clone(), merged);
        }
    }

    for var in branch_local {
        tracker.versions.remove(&var);
    }
    forward_decls
}

/// Remove any forward-declaration of `var` nested inside `lines`. Used when a
/// merged version is hoisted to an enclosing scope: its declaration emitted by a
/// nested branch must not remain inside that branch.
fn remove_forward_declarations(lines: &mut Vec<Line>, var: &str) {
    let mut i = 0;
    while i < lines.len() {
        if matches!(&lines[i], Line::ForwardDeclaration { var: decl, .. } if decl == var) {
            lines.remove(i);
        } else {
            for block in lines[i].nested_blocks_mut() {
                remove_forward_declarations(block, var);
            }
            i += 1;
        }
    }
}

fn versioned(var: &str, version: usize) -> Var {
    format!("@mut_{var}_{version}")
}

fn forward_decl(var: &str) -> Line {
    Line::ForwardDeclaration {
        var: var.to_string(),
        is_mutable: false,
    }
}

fn copy_var(target: &str, source: &str) -> Line {
    Line::Statement {
        targets: vec![AssignmentTarget::Var {
            var: target.to_string(),
            is_mutable: false,
        }],
        value: Expression::var(source.to_string()),
        location: SourceLocation {
            file_id: 0,
            line_number: 0,
        },
    }
}

/// Whether a block always ends by leaving the current function (return / panic),
/// directly or through nested blocks that all do so.
fn ends_with_early_exit(block: &[Line]) -> bool {
    match block.last() {
        Some(Line::FunctionRet { .. } | Line::Panic { .. }) => true,
        Some(last) => {
            let nested = last.nested_blocks();
            !nested.is_empty() && nested.iter().all(|b| ends_with_early_exit(b))
        }
        None => false,
    }
}

/// Rewrite every variable READ inside `expr` to its current version.
fn rename_reads(expr: &mut Expression, tracker: &Tracker) {
    match expr {
        Expression::Value(simple) => rename_simple_read(simple, tracker),
        Expression::ArrayAccess { array, index } => {
            rename_simple_read(array, tracker);
            for idx in index {
                rename_reads(idx, tracker);
            }
        }
        Expression::MathExpr(_, args) | Expression::FunctionCall { args, .. } => {
            for arg in args {
                rename_reads(arg, tracker);
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                rename_reads(idx, tracker);
            }
        }
        Expression::Lambda { body, .. } => rename_reads(body, tracker),
        Expression::HintWitness { ptr, .. } => rename_reads(ptr, tracker),
    }
}

fn rename_simple_read(simple: &mut SimpleExpr, tracker: &Tracker) {
    if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simple {
        *var = tracker.current_name(var);
    }
}
