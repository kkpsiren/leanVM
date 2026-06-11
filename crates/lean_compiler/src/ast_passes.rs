//! AST-level helpers and validity checks over the parsed [`Program`] AST.

use crate::{lang::*, parser::ConstArrayValue};
use lean_vm::BooleanExpr;
use std::collections::{BTreeMap, BTreeSet};

/// Returns (internal_vars, external_vars)
pub fn find_variable_usage(
    lines: &[Line],
    const_arrays: &BTreeMap<String, ConstArrayValue>,
) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let mut internal_vars = BTreeSet::new();
    let mut external_vars = BTreeSet::new();

    let on_new_expr = |expr: &Expression, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
        for var in vars_in_expression(expr, const_arrays) {
            if !internal_vars.contains(&var) && !const_arrays.contains_key(&var) {
                external_vars.insert(var);
            }
        }
    };

    let on_new_boolean =
        |boolean: &BooleanExpr<Expression>, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
            on_new_expr(&boolean.left, internal_vars, external_vars);
            on_new_expr(&boolean.right, internal_vars, external_vars);
        };

    for line in lines {
        match line {
            Line::ForwardDeclaration { var, .. } => {
                internal_vars.insert(var.clone());
            }
            Line::Match { value, arms, .. } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                // Arms are analyzed independently: a var read from the enclosing
                // scope in one arm stays external even if a sibling arm assigns a
                // same-named local.
                let arm_usages: Vec<_> = arms
                    .iter()
                    .map(|(_, statements)| find_variable_usage(statements, const_arrays))
                    .collect();
                for (_, arm_external) in &arm_usages {
                    external_vars.extend(arm_external.iter().filter(|v| !internal_vars.contains(*v)).cloned());
                }
                for (arm_internal, _) in arm_usages {
                    internal_vars.extend(arm_internal.into_iter().filter(|v| !external_vars.contains(v)));
                }
            }
            Line::Statement { targets, value, .. } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            if !external_vars.contains(var) {
                                internal_vars.insert(var.clone());
                            }
                        }
                        AssignmentTarget::ArrayAccess { array, index } => {
                            if let Some(array_name) = array.as_var() {
                                assert!(!const_arrays.contains_key(array_name), "Cannot assign to const array");
                                if !internal_vars.contains(array_name) {
                                    external_vars.insert(array_name.clone());
                                }
                            }
                            on_new_expr(index, &internal_vars, &mut external_vars);
                        }
                    }
                }
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                on_new_boolean(condition, &internal_vars, &mut external_vars);

                let (then_internal, then_external) = find_variable_usage(then_branch, const_arrays);
                let (else_internal, else_external) = find_variable_usage(else_branch, const_arrays);

                external_vars.extend(
                    then_external
                        .union(&else_external)
                        .filter(|v| !internal_vars.contains(*v))
                        .cloned(),
                );
                internal_vars.extend(
                    then_internal
                        .union(&else_internal)
                        .filter(|v| !external_vars.contains(*v))
                        .cloned(),
                );
            }
            Line::Assert { boolean, .. } => {
                on_new_boolean(boolean, &internal_vars, &mut external_vars);
            }
            Line::FunctionRet { return_data } => {
                for ret in return_data {
                    on_new_expr(ret, &internal_vars, &mut external_vars);
                }
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                ..
            } => {
                let (body_internal, body_external) = find_variable_usage(body, const_arrays);
                internal_vars.extend(body_internal);
                internal_vars.insert(iterator.clone());
                external_vars.extend(body_external.difference(&internal_vars).cloned());
                on_new_expr(start, &internal_vars, &mut external_vars);
                on_new_expr(end, &internal_vars, &mut external_vars);
            }
            Line::Panic { .. } | Line::LocationReport { .. } => {}
        }
    }

    (internal_vars, external_vars)
}

pub fn vars_in_expression(expr: &Expression, const_arrays: &BTreeMap<String, ConstArrayValue>) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    match expr {
        Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var))) => {
            vars.insert(var.clone());
        }
        Expression::ArrayAccess { array, .. } => {
            if let Some(name) = array.as_var()
                && !const_arrays.contains_key(name)
            {
                vars.insert(name.clone());
            }
        }
        _ => {}
    }
    for inner_expr in expr.inner_exprs() {
        vars.extend(vars_in_expression(inner_expr, const_arrays));
    }
    vars
}

pub enum VarTransform {
    ReplaceWithExpr(SimpleExpr),
    Rename(String),
    Keep,
}

impl VarTransform {
    fn apply_to_var(self, var: &mut Var) {
        match self {
            VarTransform::ReplaceWithExpr(SimpleExpr::Memory(VarOrConstMallocAccess::Var(new_var))) => {
                *var = new_var;
            }
            VarTransform::ReplaceWithExpr(_) => {
                panic!("Cannot replace variable with non-variable expression in this context");
            }
            VarTransform::Rename(new_name) => {
                *var = new_name;
            }
            VarTransform::Keep => {}
        }
    }
}

pub fn transform_vars_in_simple_expr(simple_expr: &mut SimpleExpr, transform: &impl Fn(&Var) -> VarTransform) {
    if let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simple_expr {
        match transform(var) {
            VarTransform::ReplaceWithExpr(replacement) => {
                *simple_expr = replacement;
            }
            VarTransform::Rename(new_name) => {
                *var = new_name;
            }
            VarTransform::Keep => {}
        }
    }
}

pub fn transform_vars_in_expr(expr: &mut Expression, transform: &impl Fn(&Var) -> VarTransform) {
    match expr {
        Expression::Value(value) => {
            transform_vars_in_simple_expr(value, transform);
        }
        Expression::ArrayAccess { array, .. } => {
            transform_vars_in_simple_expr(array, transform);
        }
        Expression::Len { array, .. } => {
            transform(array).apply_to_var(array);
        }
        Expression::MathExpr(_, _) | Expression::FunctionCall { .. } | Expression::HintWitness { .. } => {}
        Expression::Lambda { param, .. } => {
            transform(param).apply_to_var(param);
        }
    }
    for inner_expr in expr.inner_exprs_mut() {
        transform_vars_in_expr(inner_expr, transform);
    }
}

pub fn transform_vars_in_lines(lines: &mut [Line], transform: &impl Fn(&Var) -> VarTransform) {
    for line in lines {
        for expr in line.expressions_mut() {
            transform_vars_in_expr(expr, transform);
        }
        for block in line.nested_blocks_mut() {
            transform_vars_in_lines(block, transform);
        }
        match line {
            Line::ForwardDeclaration { var, .. } => {
                transform(var).apply_to_var(var);
            }
            Line::Statement { targets, .. } => {
                for target in targets {
                    match target {
                        AssignmentTarget::Var { var, .. } => {
                            transform(var).apply_to_var(var);
                        }
                        AssignmentTarget::ArrayAccess { array, .. } => {
                            transform_vars_in_simple_expr(array, transform);
                        }
                    }
                }
            }
            Line::ForLoop { iterator, .. } => {
                transform(iterator).apply_to_var(iterator);
            }
            _ => {}
        }
    }
}

/// True if the block is guaranteed to leave the enclosing function (return or
/// panic) on every path through its last statement.
pub fn ends_with_early_exit(block: &[Line]) -> bool {
    match block.last() {
        Some(Line::Panic { .. }) | Some(Line::FunctionRet { .. }) => true,
        // A loop body may run zero times, so a trailing loop never guarantees an exit.
        Some(Line::ForLoop { .. }) => false,
        Some(last) => {
            let nested = last.nested_blocks();
            !nested.is_empty() && nested.iter().all(|b| ends_with_early_exit(b))
        }
        None => false,
    }
}

pub fn check_no_dead_code(body: &[Line], function_name: &str) -> Result<(), String> {
    for (i, line) in body.iter().enumerate() {
        let exit_kind = match line {
            Line::FunctionRet { .. } => Some("return"),
            Line::Panic { .. } => Some("panic"),
            _ => None,
        };
        if let Some(kind) = exit_kind
            && i + 1 < body.len()
        {
            return Err(format!("function `{function_name}`: unreachable code after `{kind}`"));
        }
        for nested in line.nested_blocks() {
            check_no_dead_code(nested, function_name)?;
        }
    }
    Ok(())
}

pub fn check_program_scoping(program: &Program) -> Result<(), String> {
    for function in program.functions.values() {
        let mut scope = Scope { vars: BTreeSet::new() };
        for arg in function.arguments.iter() {
            scope.vars.insert(arg.name.clone());
        }
        let mut ctx = Context {
            scopes: vec![scope],
            const_arrays: program.const_arrays.clone(),
        };

        check_block_scoping(&function.body, &mut ctx)?;
    }
    Ok(())
}

fn check_block_scoping(block: &[Line], ctx: &mut Context) -> Result<(), String> {
    for line in block.iter() {
        match line {
            Line::ForwardDeclaration { var, .. } => {
                if ctx.defines(var) {
                    let in_current_scope = ctx.scopes.last().is_some_and(|s| s.vars.contains(var));
                    return Err(if in_current_scope {
                        format!("Variable '{var}' declared multiple times in the same scope")
                    } else {
                        format!("Declaration of '{var}' shadows a name visible in an enclosing scope")
                    });
                }
                ctx.add_var(var);
            }
            Line::Match { value, arms, .. } => {
                check_expr_scoping(value, ctx)?;
                for (_, arm) in arms {
                    ctx.scopes.push(Scope { vars: BTreeSet::new() });
                    check_block_scoping(arm, ctx)?;
                    ctx.scopes.pop();
                }
            }
            Line::Statement { targets, value, .. } => {
                check_expr_scoping(value, ctx)?;
                for target in targets {
                    if let AssignmentTarget::Var { var, .. } = target
                        && !ctx.defines(var)
                    {
                        ctx.add_var(var);
                    }
                }
                for target in targets {
                    if let AssignmentTarget::ArrayAccess { array, index } = target {
                        check_simple_expr_scoping(array, ctx)?;
                        check_expr_scoping(index, ctx)?;
                    }
                }
            }
            Line::Assert { boolean, .. } => {
                check_boolean_scoping(boolean, ctx)?;
            }
            Line::IfCondition {
                condition,
                then_branch,
                else_branch,
                location: _,
            } => {
                check_boolean_scoping(condition, ctx)?;
                for branch in [then_branch, else_branch] {
                    ctx.scopes.push(Scope { vars: BTreeSet::new() });
                    check_block_scoping(branch, ctx)?;
                    ctx.scopes.pop();
                }
            }
            Line::ForLoop {
                iterator,
                start,
                end,
                body,
                loop_kind: _,
                location: _,
            } => {
                check_expr_scoping(start, ctx)?;
                check_expr_scoping(end, ctx)?;
                let mut new_scope_vars = BTreeSet::new();
                new_scope_vars.insert(iterator.clone());
                ctx.scopes.push(Scope { vars: new_scope_vars });
                check_block_scoping(body, ctx)?;
                ctx.scopes.pop();
            }
            Line::FunctionRet { return_data } => {
                for expr in return_data {
                    check_expr_scoping(expr, ctx)?;
                }
            }
            Line::Panic { .. } | Line::LocationReport { .. } => {}
        }
    }
    Ok(())
}

fn check_expr_scoping(expr: &Expression, ctx: &Context) -> Result<(), String> {
    match expr {
        Expression::Value(simple_expr) => check_simple_expr_scoping(simple_expr, ctx),
        Expression::Lambda { param, body } => {
            // Lambda binders cannot shadow enclosing names (later passes substitute by name).
            if ctx.defines(param) {
                return Err(format!(
                    "Lambda parameter '{param}' shadows a name visible in an enclosing scope"
                ));
            }
            let mut lambda_ctx = Context::new();
            lambda_ctx.scopes = ctx.scopes.clone();
            lambda_ctx.const_arrays = ctx.const_arrays.clone();
            lambda_ctx.add_var(param);
            check_expr_scoping(body, &lambda_ctx)
        }
        Expression::ArrayAccess { array, index } => {
            for idx in index {
                check_expr_scoping(idx, ctx)?;
            }
            if let Some(name) = array.as_var()
                && !ctx.const_arrays.contains_key(name)
                && !ctx.defines(name)
            {
                return Err(format!("Variable used but not defined: {name}"));
            }
            Ok(())
        }
        _ => {
            for inner_expr in expr.inner_exprs() {
                check_expr_scoping(inner_expr, ctx)?;
            }
            Ok(())
        }
    }
}

fn check_simple_expr_scoping(expr: &SimpleExpr, ctx: &Context) -> Result<(), String> {
    match expr {
        SimpleExpr::Memory(VarOrConstMallocAccess::Var(v)) => {
            if !ctx.defines(v) {
                return Err(format!("Variable used but not defined: {v}"));
            }
        }
        SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) | SimpleExpr::Constant(_) => {}
    }
    Ok(())
}

fn check_boolean_scoping(boolean: &BooleanExpr<Expression>, ctx: &Context) -> Result<(), String> {
    check_expr_scoping(&boolean.left, ctx)?;
    check_expr_scoping(&boolean.right, ctx)
}
