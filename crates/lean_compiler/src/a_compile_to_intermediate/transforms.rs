//! Compile-time transformations (first stage): `match_range` -> `match`,
//! inlining of `@inline` functions, specialization of `Const`-arg functions,
//! `unroll` expansion, and constant folding / propagation.
//!
//! KNOWN LIMITATION: a (directly or indirectly) self-recursive `@inline`
//! function makes inlining loop forever and OOM.

use crate::{F, ast_passes::*, lang::*, parser::ConstArrayValue};
use backend::*;
use lean_vm::SourceLocation;
use std::collections::{BTreeMap, BTreeSet};

const MAX_UNROLL_ITERATIONS: usize = 1 << 20;

#[derive(Default)]
struct NameGenerators {
    unroll: Counter,
    inline: Counter,
    /// Specialization key (e.g. `f(a=3)`) -> final function name.
    specializations: BTreeMap<String, String>,
}

pub(super) fn compile_time_transform_in_program(program: &mut Program) -> Result<(), String> {
    let mut names = NameGenerators::default();
    let const_arrays = program.const_arrays.clone();

    let inlined_functions: BTreeMap<_, _> = program
        .functions
        .iter()
        .filter(|(_, func)| func.inlined)
        .map(|(name, func)| (name.clone(), func.clone()))
        .collect();

    for func in inlined_functions.values() {
        if func.has_const_arguments() {
            return Err(format!(
                "Inlined function should not have \"Const\" arguments (function \"{}\")",
                func.name
            ));
        }
        check_inline_returns(&func.body, &func.name)?;
    }

    // Process all functions, including newly created specialized ones.
    let mut processed: BTreeSet<String> = BTreeSet::new();
    loop {
        let to_process: Vec<_> = program
            .functions
            .iter()
            .filter(|(name, func)| !func.inlined && !func.has_const_arguments() && !processed.contains(*name))
            .map(|(name, _)| name.clone())
            .collect();

        if to_process.is_empty() {
            break;
        }

        let existing_functions = program.functions.clone();
        for func_name in to_process {
            processed.insert(func_name.clone());
            let func = program.functions.get_mut(&func_name).unwrap();
            let mut new_functions = BTreeMap::new();
            // Soundness: reads of a variable that is mutable anywhere in this
            // function must never be const-folded (a runtime branch may reassign
            // it). Kept up to date as inlining/unrolling splice in their mutables.
            let mut mutable_vars = collect_mutable_vars(&func.body);
            compile_time_transform_in_lines(
                &mut func.body,
                &const_arrays,
                &existing_functions,
                &inlined_functions,
                &mut new_functions,
                &mut names,
                &BTreeMap::new(),
                &mut mutable_vars,
            )?;
            for (name, new_func) in new_functions {
                program.functions.entry(name).or_insert(new_func);
            }
        }
    }
    Ok(())
}

/// All variables declared mutable (`x: Mut`) anywhere in this block (nested too).
fn collect_mutable_vars(lines: &[Line]) -> BTreeSet<Var> {
    let mut mutable_vars = BTreeSet::new();
    collect_mutable_vars_helper(lines, &mut mutable_vars);
    mutable_vars
}

fn collect_mutable_vars_helper(lines: &[Line], mutable_vars: &mut BTreeSet<Var>) {
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, is_mutable: true } => {
                mutable_vars.insert(var.clone());
            }
            Line::Statement { targets, .. } => {
                for target in targets {
                    if let AssignmentTarget::Var { var, is_mutable: true } = target {
                        mutable_vars.insert(var.clone());
                    }
                }
            }
            _ => {}
        }
        for block in line.nested_blocks() {
            collect_mutable_vars_helper(block, mutable_vars);
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn compile_time_transform_in_lines(
    lines: &mut Vec<Line>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    existing_functions: &BTreeMap<String, Function>,
    inlined_functions: &BTreeMap<String, Function>,
    new_functions: &mut BTreeMap<String, Function>,
    names: &mut NameGenerators,
    parent_const_var_exprs: &BTreeMap<Var, F>,
    mutable_vars: &mut BTreeSet<Var>,
) -> Result<(), String> {
    let mut const_var_exprs: BTreeMap<Var, F> = parent_const_var_exprs.clone();

    let mut i = 0;
    while i < lines.len() {
        let line = &mut lines[i];

        // match_range must be expanded before any expression transform: lambda
        // bodies contain bound variables that aren't in scope yet.
        if let Line::Statement {
            targets,
            value,
            location,
        } = line
            && let Some(expanded) = try_expand_match_range(value, targets, *location, const_arrays)?
        {
            lines.splice(i..=i, expanded);
            continue;
        }

        for expr in line.expressions_mut() {
            substitute_const_vars_in_expr(expr, &const_var_exprs);
            compile_time_transform_in_expr(expr, const_arrays)?;
        }

        // Extract nested inlined/const-arg calls into temps, e.g.
        // `x = a + inlined(b)` -> `tmp = inlined(b); x = a + tmp`.
        if let Some(new_lines) =
            extract_preprocessed_calls(line, inlined_functions, existing_functions, &mut names.inline)?
        {
            lines.splice(i..=i, new_lines);
            continue;
        }

        match line {
            Line::Statement { targets, value, .. } => {
                if let Some(inlined) =
                    try_inline_call(value, targets, inlined_functions, const_arrays, &mut names.inline)?
                {
                    collect_mutable_vars_helper(&inlined, mutable_vars);
                    lines.splice(i..=i, inlined);
                    continue;
                }
                // Specialize direct const-arg calls, e.g. `double(1)` -> `__spec0_double_a_1()`.
                if let Expression::FunctionCall {
                    function_name, args, ..
                } = value
                    && let Some(func) = existing_functions.get(function_name.as_str())
                    && func.has_const_arguments()
                {
                    if args.len() != func.arguments.len() {
                        return Err(format!(
                            "Function '{}' expects {} arguments, got {}",
                            function_name,
                            func.arguments.len(),
                            args.len()
                        ));
                    }
                    let mut const_evals = Vec::new();
                    for (arg_expr, arg) in args.iter().zip(&func.arguments) {
                        if arg.is_const {
                            if let Some(const_eval) = arg_expr.as_scalar() {
                                const_evals.push((arg.name.clone(), const_eval));
                            } else {
                                return Err(format!(
                                    "Cannot evaluate const argument '{}' for function '{}'",
                                    arg.name, function_name
                                ));
                            }
                        }
                    }
                    // The key is collision-free: its separators (`(`, `=`, `,`)
                    // can't appear in identifiers/constants. The final name embeds
                    // a unique index since names are identifier-only.
                    let spec_key = format!(
                        "{function_name}({})",
                        const_evals
                            .iter()
                            .map(|(v, c)| format!("{v}={c}"))
                            .collect::<Vec<_>>()
                            .join(",")
                    );
                    let spec_index = names.specializations.len();
                    let const_funct_name = names
                        .specializations
                        .entry(spec_key)
                        .or_insert_with(|| {
                            format!(
                                "__spec{spec_index}_{function_name}_{}",
                                const_evals
                                    .iter()
                                    .map(|(v, c)| format!("{v}_{c}"))
                                    .collect::<Vec<_>>()
                                    .join("_")
                            )
                        })
                        .clone();
                    *function_name = const_funct_name.clone();
                    *args = args
                        .iter()
                        .zip(&func.arguments)
                        .filter(|(_, arg)| !arg.is_const)
                        .map(|(e, _)| e.clone())
                        .collect();
                    if !new_functions.contains_key(&const_funct_name)
                        && !existing_functions.contains_key(&const_funct_name)
                    {
                        let mut new_body = func.body.clone();
                        replace_vars_by_const_in_lines(&mut new_body, &const_evals.iter().cloned().collect())?;
                        new_functions.insert(
                            const_funct_name.clone(),
                            Function {
                                name: const_funct_name,
                                arguments: func.arguments.iter().filter(|a| !a.is_const).cloned().collect(),
                                inlined: false,
                                body: new_body,
                                n_returned_vars: func.n_returned_vars,
                            },
                        );
                    }
                }
                if targets.len() == 1
                    && let AssignmentTarget::Var { var, is_mutable: false } = &targets[0]
                    && !mutable_vars.contains(var)
                    && let Some(value_const) = value.as_scalar()
                {
                    const_var_exprs.insert(var.clone(), value_const);
                }
            }

            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                if let Some(constant_condition) = condition.try_eval(|expr| expr.as_scalar()) {
                    let chosen_branch = if constant_condition { then_branch } else { else_branch }.clone();
                    lines.splice(i..=i, chosen_branch);
                    continue;
                }
            }

            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                loop_kind: LoopKind::Unroll,
                location,
            } => {
                let (Some(start), Some(end)) = (start.as_scalar(), end.as_scalar()) else {
                    return Err(format!(
                        "line {}: Cannot unroll loop with non-constant bounds",
                        location
                    ));
                };
                let (start_u, end_u) = (start.to_usize(), end.to_usize());
                let count = end_u.saturating_sub(start_u);
                if count > MAX_UNROLL_ITERATIONS {
                    return Err(format!(
                        "line {location}: `unroll` loop is too large ({count} iterations; max {MAX_UNROLL_ITERATIONS})"
                    ));
                }
                let unroll_index = names.unroll.get_next();
                let (internal_vars, _) = find_variable_usage(body, const_arrays);
                // An outer mutable must keep its name across iterations (usage
                // analysis classifies it internal when written before read);
                // body-local mutables stay per-iteration.
                let body_muts = collect_mutable_vars(body);
                let internal_vars: BTreeSet<Var> = internal_vars
                    .into_iter()
                    .filter(|v| body_muts.contains(v) || !mutable_vars.contains(v))
                    .collect();
                let iterator = iterator.clone();
                let body = body.clone();
                let mut unrolled = Vec::new();
                for j in start_u..end_u {
                    let mut body_copy = body.clone();
                    replace_vars_for_unroll(&mut body_copy, &iterator, unroll_index, j, &internal_vars);
                    unrolled.extend(body_copy);
                }
                collect_mutable_vars_helper(&unrolled, mutable_vars);
                lines.splice(i..=i, unrolled);
                continue;
            }
            _ => {}
        }

        // Propagate const vars into blocks that stay inline.
        let parent = if matches!(
            lines[i],
            Line::IfCondition { .. }
                | Line::Match { .. }
                | Line::ForLoop {
                    loop_kind: LoopKind::Unroll,
                    ..
                }
        ) {
            &const_var_exprs
        } else {
            &BTreeMap::new()
        };
        for block in lines[i].nested_blocks_mut() {
            compile_time_transform_in_lines(
                block,
                const_arrays,
                existing_functions,
                inlined_functions,
                new_functions,
                names,
                parent,
                mutable_vars,
            )?;
        }

        i += 1;
    }
    Ok(())
}

/// Expand `match_range(value, range(a, b), lambda i: e1, range(b, c), lambda i: e2, ...)`
/// into forward declarations + a `Line::Match`.
fn try_expand_match_range(
    value: &Expression,
    targets: &[AssignmentTarget],
    location: SourceLocation,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> Result<Option<Vec<Line>>, String> {
    let Expression::FunctionCall {
        function_name, args, ..
    } = value
    else {
        return Ok(None);
    };
    if function_name != "match_range" {
        return Ok(None);
    }
    if args.len() < 3 || (args.len() - 1) % 2 != 0 {
        return Err("match_range expects: value, range, lambda, range, lambda, ...".to_string());
    }

    for t in targets {
        if let AssignmentTarget::Var { var, is_mutable: true } = t {
            return Err(format!(
                "match_range results are always immutable, cannot use ': Mut' for '{var}'"
            ));
        }
    }

    let mut result = vec![];
    let arm_targets: Vec<_> = targets
        .iter()
        .map(|t| match t {
            AssignmentTarget::Var { var, .. } => {
                result.push(Line::ForwardDeclaration {
                    var: var.clone(),
                    is_mutable: false,
                });
                AssignmentTarget::Var {
                    var: var.clone(),
                    is_mutable: false,
                }
            }
            other => other.clone(),
        })
        .collect();

    let mut arms = vec![];
    let mut expected_start: Option<usize> = None;

    for (range_arg, lambda_arg) in args[1..].chunks(2).map(|c| (&c[0], &c[1])) {
        let Expression::FunctionCall {
            function_name: rf,
            args: ra,
            ..
        } = range_arg
        else {
            return Err("match_range: expected range(start, end)".into());
        };
        if rf != "range" || ra.len() != 2 {
            return Err("match_range: expected range(start, end)".into());
        }
        let start = ra[0]
            .compile_time_eval(const_arrays)
            .ok_or(format!("match_range: range start must be constant (at {location})"))?
            .to_usize();
        let end = ra[1]
            .compile_time_eval(const_arrays)
            .ok_or(format!("match_range: range end must be constant (at {location})"))?
            .to_usize();

        let Expression::Lambda { param, body } = lambda_arg else {
            return Err("match_range: expected lambda".into());
        };

        // Without targets each arm is a bare expression statement, only
        // printable/meaningful when the expression is a call.
        if targets.is_empty() && !matches!(body.as_ref(), Expression::FunctionCall { .. }) {
            return Err(format!(
                "match_range at {location}: used as a statement, so each lambda body must be a \
                 function call (its value would be discarded otherwise)"
            ));
        }

        if let Some(exp) = expected_start
            && start != exp
        {
            return Err(format!(
                "match_range: ranges must be continuous, expected start {exp} but got {start}"
            ));
        }
        expected_start = Some(end);

        for case_val in start..end {
            let mut expr = body.as_ref().clone();
            substitute_lambda_param(&mut expr, param, case_val);
            arms.push((
                case_val,
                vec![Line::Statement {
                    targets: arm_targets.clone(),
                    value: expr,
                    location,
                }],
            ));
        }
    }

    if arms.is_empty() {
        return Err(format!("match_range at {location}: all ranges are empty (no arms)"));
    }

    result.push(Line::Match {
        value: args[0].clone(),
        arms,
        location,
    });
    Ok(Some(result))
}

fn substitute_lambda_param(expr: &mut Expression, param: &str, value: usize) {
    if let Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(v))) = expr
        && v == param
    {
        *expr = Expression::scalar(F::from_usize(value));
        return;
    }
    for inner in expr.inner_exprs_mut() {
        substitute_lambda_param(inner, param, value);
    }
}

fn try_inline_call(
    value: &Expression,
    targets: &[AssignmentTarget],
    inlined_functions: &BTreeMap<String, Function>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    inline_counter: &mut Counter,
) -> Result<Option<Vec<Line>>, String> {
    let Expression::FunctionCall {
        function_name,
        args,
        location,
    } = value
    else {
        return Ok(None);
    };
    let Some(func) = inlined_functions.get(function_name) else {
        return Ok(None);
    };

    if args.len() != func.arguments.len() {
        return Err(format!(
            "Function '{}' expects {} arguments, got {}",
            function_name,
            func.arguments.len(),
            args.len()
        ));
    }
    if targets.len() != func.n_returned_vars {
        return Err(format!(
            "Expected {} returned vars (and not {}) in call to {}",
            func.n_returned_vars,
            targets.len(),
            function_name
        ));
    }

    // If any arg is not a simple value, extract it into a temp first.
    if args.iter().any(|a| !matches!(a, Expression::Value(_))) {
        let mut new_lines = vec![];
        let mut new_args = vec![];
        for arg in args {
            if let Expression::Value(v) = arg {
                new_args.push(Expression::Value(v.clone()));
            } else {
                let tmp = format!("__inline_arg_{}", inline_counter.get_next());
                new_lines.push(Line::ForwardDeclaration {
                    var: tmp.clone(),
                    is_mutable: false,
                });
                new_lines.push(Line::Statement {
                    targets: vec![AssignmentTarget::Var {
                        var: tmp.clone(),
                        is_mutable: false,
                    }],
                    value: arg.clone(),
                    location: *location,
                });
                new_args.push(Expression::var(tmp));
            }
        }
        new_lines.push(Line::Statement {
            targets: targets.to_vec(),
            value: Expression::FunctionCall {
                function_name: function_name.clone(),
                args: new_args,
                location: *location,
            },
            location: *location,
        });
        return Ok(Some(new_lines));
    }

    let args_map: BTreeMap<Var, SimpleExpr> = func
        .arguments
        .iter()
        .zip(args)
        .map(|(arg, expr)| {
            let Expression::Value(v) = expr else { unreachable!() };
            (arg.name.clone(), v.clone())
        })
        .collect();

    let mut body = func.body.clone();
    inline_lines(&mut body, &args_map, const_arrays, targets, inline_counter.get_next());
    Ok(Some(body))
}

/// Hoist nested inlined/const-arg calls into temp vars, so they become direct
/// calls the main loop can process.
fn extract_preprocessed_calls(
    line: &mut Line,
    inlined_functions: &BTreeMap<String, Function>,
    all_functions: &BTreeMap<String, Function>,
    counter: &mut Counter,
) -> Result<Option<Vec<Line>>, String> {
    fn needs_preprocessing(name: &str, inlined: &BTreeMap<String, Function>, all: &BTreeMap<String, Function>) -> bool {
        inlined.contains_key(name) || all.get(name).is_some_and(|f| f.has_const_arguments())
    }

    fn extract(
        expr: &mut Expression,
        inlined: &BTreeMap<String, Function>,
        all: &BTreeMap<String, Function>,
        counter: &mut Counter,
        out: &mut Vec<Line>,
    ) -> Result<(), String> {
        for inner in expr.inner_exprs_mut() {
            extract(inner, inlined, all, counter, out)?;
        }
        if let Expression::FunctionCall {
            function_name,
            args,
            location,
        } = expr
            && needs_preprocessing(function_name, inlined, all)
        {
            let func = inlined.get(function_name).or_else(|| all.get(function_name));
            if let Some(f) = func
                && f.n_returned_vars != 1
            {
                return Err(format!(
                    "Function '{}' with {} return values cannot appear in expression",
                    function_name, f.n_returned_vars
                ));
            }
            let tmp = format!("__extract_tmp_{}", counter.get_next());
            out.push(Line::ForwardDeclaration {
                var: tmp.clone(),
                is_mutable: false,
            });
            out.push(Line::Statement {
                targets: vec![AssignmentTarget::Var {
                    var: tmp.clone(),
                    is_mutable: false,
                }],
                value: Expression::FunctionCall {
                    function_name: function_name.clone(),
                    args: args.clone(),
                    location: *location,
                },
                location: *location,
            });
            *expr = Expression::var(tmp);
        }
        Ok(())
    }

    let mut extractions = vec![];
    // For a direct preprocessed call, only hoist from its arguments; otherwise from all expressions.
    match line {
        Line::Statement {
            value: Expression::FunctionCall {
                function_name, args, ..
            },
            ..
        } if needs_preprocessing(function_name, inlined_functions, all_functions) => {
            for arg in args.iter_mut() {
                extract(arg, inlined_functions, all_functions, counter, &mut extractions)?;
            }
        }
        _ => {
            for expr in line.expressions_mut() {
                extract(expr, inlined_functions, all_functions, counter, &mut extractions)?;
            }
        }
    }

    if extractions.is_empty() {
        Ok(None)
    } else {
        extractions.push(line.clone());
        Ok(Some(extractions))
    }
}

fn compile_time_transform_in_expr(
    expr: &mut Expression,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> Result<bool, String> {
    if expr.is_scalar() {
        return Ok(false);
    }
    let mut changed = false;
    for inner_expr in expr.inner_exprs_mut() {
        changed |= compile_time_transform_in_expr(inner_expr, const_arrays)?;
    }
    if let Some(scalar) = expr.compile_time_eval(const_arrays) {
        *expr = Expression::scalar(scalar);
        changed = true;
    } else if let Expression::Len { .. } = &*expr {
        return Err("Cannot call len() on a scalar value".to_string());
    } else if let Expression::MathExpr(op, args) = &*expr
        && args.iter().all(Expression::is_scalar)
    {
        return Err(format!("compile-time `{op}` failed"));
    }
    Ok(changed)
}

fn substitute_const_vars_in_expr(expr: &mut Expression, const_var_exprs: &BTreeMap<Var, F>) -> bool {
    if let Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var))) = expr
        && let Some(replacement) = const_var_exprs.get(var)
    {
        *expr = Expression::scalar(*replacement);
        return true;
    }

    let mut changed = false;
    for inner in expr.inner_exprs_mut() {
        changed |= substitute_const_vars_in_expr(inner, const_var_exprs);
    }
    changed
}

/// Variables defined outside this block but reassigned inside it.
fn find_modified_external_vars(
    lines: &[Line],
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    outer_mut_vars: &BTreeSet<Var>,
) -> BTreeSet<Var> {
    let (mut internal_vars, mut external_vars) = find_variable_usage(lines, const_arrays);

    // Enclosing-scope mutables are always external, even if only written here.
    for v in outer_mut_vars {
        if !const_arrays.contains_key(v) {
            internal_vars.remove(v);
            external_vars.insert(v.clone());
        }
    }

    let mut modified_external_vars = BTreeSet::new();
    find_assigned_external_vars_helper(
        lines,
        const_arrays,
        &internal_vars,
        &external_vars,
        &mut modified_external_vars,
    );

    modified_external_vars
}

fn find_assigned_external_vars_helper(
    lines: &[Line],
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    internal_vars: &BTreeSet<Var>,
    external_vars: &BTreeSet<Var>,
    modified_external_vars: &mut BTreeSet<Var>,
) {
    for line in lines {
        match line {
            Line::Statement { targets, .. } => {
                for target in targets {
                    if let AssignmentTarget::Var { var, is_mutable } = target {
                        // is_mutable: true is the initial declaration, not a modification.
                        if !*is_mutable
                            && external_vars.contains(var)
                            && !internal_vars.contains(var)
                            && !const_arrays.contains_key(var)
                        {
                            modified_external_vars.insert(var.clone());
                        }
                    }
                }
            }
            _ => {
                for block in line.nested_blocks() {
                    find_assigned_external_vars_helper(
                        block,
                        const_arrays,
                        internal_vars,
                        external_vars,
                        modified_external_vars,
                    );
                }
            }
        }
    }
}

/// Reject any `range` / `parallel_range` loop that reassigns an enclosing-scope
/// mutable ("loop-carried mutable").
pub(super) fn check_no_loop_carried_mutables(program: &Program) -> Result<(), String> {
    for func in program.functions.values() {
        check_loop_carried_mutables_in_lines(&func.body, &program.const_arrays, &BTreeSet::new())?;
    }
    Ok(())
}

fn check_loop_carried_mutables_in_lines(
    lines: &[Line],
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    outer_mut_vars: &BTreeSet<Var>,
) -> Result<(), String> {
    let mut local_mut_vars = outer_mut_vars.clone();
    for line in lines {
        match line {
            Line::ForLoop {
                body,
                loop_kind: LoopKind::Range | LoopKind::ParallelRange,
                location,
                ..
            } => {
                check_loop_carried_mutables_in_lines(body, const_arrays, &local_mut_vars)?;
                let modified_vars = find_modified_external_vars(body, const_arrays, &local_mut_vars);
                if !modified_vars.is_empty() {
                    return Err(format!(
                        "loop at {location} reassigns enclosing-scope mutable(s) {modified_vars:?}; \
                         loop-carried mutables are unsupported: use an explicit buffer (see zkDSL.md, \"For loops\")"
                    ));
                }
            }
            Line::ForLoop { body, .. } => {
                check_loop_carried_mutables_in_lines(body, const_arrays, &local_mut_vars)?;
            }
            Line::IfCondition { .. } | Line::Match { .. } => {
                for block in line.nested_blocks() {
                    check_loop_carried_mutables_in_lines(block, const_arrays, &local_mut_vars)?;
                }
            }
            Line::ForwardDeclaration { var, is_mutable: true } => {
                local_mut_vars.insert(var.clone());
            }
            Line::Statement { targets, .. } => {
                for target in targets {
                    if let AssignmentTarget::Var { var, is_mutable: true } = target {
                        local_mut_vars.insert(var.clone());
                    }
                }
            }
            _ => {}
        }
    }
    Ok(())
}

fn inline_lines(
    lines: &mut Vec<Line>,
    args: &BTreeMap<Var, SimpleExpr>,
    const_arrays: &BTreeMap<String, ConstArrayValue>,
    res: &[AssignmentTarget],
    inlining_count: usize,
) {
    let transform = |var: &Var| -> VarTransform {
        if let Some(replacement) = args.get(var) {
            VarTransform::ReplaceWithExpr(replacement.clone())
        } else if const_arrays.contains_key(var) {
            VarTransform::Keep
        } else {
            VarTransform::Rename(format!("__inlined_var_{inlining_count}_{var}"))
        }
    };

    transform_vars_in_lines(lines, &transform);
    replace_function_ret_in_lines(lines, res);
}

fn check_inline_returns(body: &[Line], func_name: &str) -> Result<(), String> {
    fn count_returns(lines: &[Line]) -> usize {
        lines
            .iter()
            .map(|line| {
                usize::from(matches!(line, Line::FunctionRet { .. }))
                    + line.nested_blocks().iter().map(|b| count_returns(b)).sum::<usize>()
            })
            .sum()
    }

    let nested_returns: usize = body
        .iter()
        .flat_map(Line::nested_blocks)
        .map(|b| count_returns(b))
        .sum();

    if nested_returns > 0 || count_returns(body) > 1 {
        return Err(format!(
            "Inline function `{func_name}` has an unsupported `return`. Inline functions support \
             exactly one `return`, placed at the end of the function's body"
        ));
    }
    Ok(())
}

fn replace_function_ret_in_lines(lines: &mut Vec<Line>, res: &[AssignmentTarget]) {
    for line in lines.iter_mut() {
        for block in line.nested_blocks_mut() {
            replace_function_ret_in_lines(block, res);
        }
    }

    let mut lines_to_replace = vec![];
    for (i, line) in lines.iter().enumerate() {
        if let Line::FunctionRet { return_data } = line {
            assert_eq!(return_data.len(), res.len());
            lines_to_replace.push((
                i,
                res.iter()
                    .zip(return_data.iter())
                    .map(|(target, expr)| Line::Statement {
                        targets: vec![target.clone()],
                        value: expr.clone(),
                        location: SourceLocation {
                            file_id: 0,
                            line_number: 0,
                        }, // TODO
                    })
                    .collect::<Vec<_>>(),
            ));
        }
    }
    for (i, new_lines) in lines_to_replace.into_iter().rev() {
        lines.splice(i..=i, new_lines);
    }
}

fn replace_vars_for_unroll(
    lines: &mut [Line],
    iterator: &Var,
    unroll_index: usize,
    iterator_value: usize,
    internal_vars: &BTreeSet<Var>,
) {
    let transform = |var: &Var| -> VarTransform {
        if var == iterator {
            VarTransform::ReplaceWithExpr(SimpleExpr::Constant(ConstExpression::from(iterator_value)))
        } else if internal_vars.contains(var) {
            VarTransform::Rename(format!("__unrolled_{unroll_index}_{iterator_value}_{var}"))
        } else {
            VarTransform::Keep
        }
    };

    transform_vars_in_lines(lines, &transform);
}

fn replace_vars_by_const_in_expr(expr: &mut Expression, map: &BTreeMap<Var, F>) -> Result<(), String> {
    match expr {
        Expression::Value(value) => match &value {
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => {
                if let Some(const_value) = map.get(var) {
                    *value = SimpleExpr::scalar(*const_value);
                }
            }
            SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) => {
                unreachable!()
            }
            SimpleExpr::Constant(_) => {}
        },
        Expression::ArrayAccess { array, index } => {
            if let Some(name) = array.as_var()
                && map.contains_key(name)
            {
                return Err(format!("Array {name} is a constant"));
            }
            for index in index {
                replace_vars_by_const_in_expr(index, map)?;
            }
        }
        Expression::MathExpr(_, args) => {
            for arg in args {
                replace_vars_by_const_in_expr(arg, map)?;
            }
        }
        Expression::FunctionCall { args, .. } => {
            for arg in args {
                replace_vars_by_const_in_expr(arg, map)?;
            }
        }
        Expression::Len { indices, .. } => {
            for idx in indices {
                replace_vars_by_const_in_expr(idx, map)?;
            }
        }
        Expression::Lambda { body, .. } => {
            replace_vars_by_const_in_expr(body, map)?;
        }
        Expression::HintWitness { .. } => {}
    }
    Ok(())
}

fn replace_vars_by_const_in_lines(lines: &mut [Line], map: &BTreeMap<Var, F>) -> Result<(), String> {
    for line in lines {
        match line {
            Line::ForwardDeclaration { var, .. } if map.contains_key(var) => {
                return Err(format!("Variable {var} is a constant"));
            }
            Line::Statement { targets, .. } => {
                for target in targets.iter() {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            if map.contains_key(var) {
                                return Err(format!("Variable {var} is a constant"));
                            }
                        }
                        AssignmentTarget::ArrayAccess { array, .. } => {
                            if let Some(name) = array.as_var()
                                && map.contains_key(name)
                            {
                                return Err(format!("Array {name} is a constant"));
                            }
                        }
                    }
                }
            }
            _ => {}
        }
        for expr in line.expressions_mut() {
            replace_vars_by_const_in_expr(expr, map)?;
        }
        for block in line.nested_blocks_mut() {
            replace_vars_by_const_in_lines(block, map)?;
        }
    }
    Ok(())
}
