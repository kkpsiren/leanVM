//! Final stage-1 pass: make the transformed program expressible in (and
//! re-parseable from) the intermediate zkDSL surface syntax. See the four
//! numbered steps in [`legalize_program`].

use crate::{ast_passes::*, lang::*, parser::ConstArrayValue};
use std::collections::{BTreeMap, BTreeSet};

pub(super) fn legalize_program(program: &mut Program) -> Result<(), String> {
    // 1. Drop forward declarations that shadow an enclosing binding (emitted by
    //    the scope-unaware `match_range` expansion).
    remove_shadowing_forward_declarations(program);
    // 2. Append an unreachable `return` to value-returning functions whose
    //    `return`s were all folded away (the parser infers the count from them).
    ensure_functions_have_a_return(program)?;
    // 3. Hoist non-variable array bases: `1234[i]` -> `ptr = 1234; ptr[i]`.
    hoist_non_var_array_bases(program);
    // 4. Reject leftover const arrays / `len()` / lambdas.
    check_no_unresolved_compile_time_constructs(program)?;
    Ok(())
}

const DUMMY_LOCATION: SourceLocation = SourceLocation {
    file_id: 0,
    line_number: 0,
};

/// The `match_range` expansion forward-declares its result variables next to
/// the generated `match`. When the variable was already declared in an
/// enclosing scope, that generated declaration shadows the enclosing one: drop
/// it so the assignment targets the enclosing binding. (User-written shadowing
/// declarations were already rejected by the earlier scoping check.)
fn remove_shadowing_forward_declarations(program: &mut Program) {
    for func in program.functions.values_mut() {
        let root_scope: BTreeSet<Var> = func.arguments.iter().map(|arg| arg.name.clone()).collect();
        remove_shadowing_decls_in_lines(&mut func.body, &mut vec![root_scope]);
    }
}

fn remove_shadowing_decls_in_lines(lines: &mut Vec<Line>, scopes: &mut Vec<BTreeSet<Var>>) {
    for mut line in std::mem::take(lines) {
        match &mut line {
            Line::ForwardDeclaration { var, .. } => {
                if scopes.iter().any(|scope| scope.contains(var)) {
                    continue; // drop the shadowing declaration
                }
                scopes.last_mut().unwrap().insert(var.clone());
            }
            Line::Statement { targets, .. } => {
                // Plain assignments also bind names (cf. `check_block_scoping`).
                let last_scope = scopes.last_mut().unwrap();
                for target in targets.iter() {
                    if let AssignmentTarget::Var { var, .. } = target
                        && !last_scope.contains(var)
                    {
                        last_scope.insert(var.clone());
                    }
                }
            }
            Line::ForLoop { iterator, body, .. } => {
                scopes.push([iterator.clone()].into_iter().collect());
                remove_shadowing_decls_in_lines(body, scopes);
                scopes.pop();
            }
            other => {
                for block in other.nested_blocks_mut() {
                    scopes.push(BTreeSet::new());
                    remove_shadowing_decls_in_lines(block, scopes);
                    scopes.pop();
                }
            }
        }
        lines.push(line);
    }
}

/// Constant folding can remove every `return` from a function whose body
/// reduces to an unconditional panic. A value-returning function must keep at
/// least one `return` through the source round trip (the parser infers the
/// count from them), so append an unreachable one. A return-less function that
/// doesn't panic on every path can fall through its end: reject it.
fn ensure_functions_have_a_return(program: &mut Program) -> Result<(), String> {
    fn contains_return(lines: &[Line]) -> bool {
        lines.iter().any(|line| {
            matches!(line, Line::FunctionRet { .. }) || line.nested_blocks().iter().any(|b| contains_return(b))
        })
    }

    for func in program.functions.values_mut() {
        if func.n_returned_vars == 0 || contains_return(&func.body) {
            continue;
        }
        if !ends_with_early_exit(&func.body) {
            return Err(format!("Cannot prove that function always returns: {}", func.name));
        }
        func.body.push(Line::FunctionRet {
            return_data: vec![Expression::zero(); func.n_returned_vars],
        });
    }
    Ok(())
}

fn hoist_non_var_array_bases(program: &mut Program) {
    let mut counter = 0;
    for func in program.functions.values_mut() {
        hoist_in_lines(&mut func.body, &mut counter);
    }
}

fn hoist_base(array: &mut SimpleExpr, hoisted: &mut Vec<Line>, counter: &mut usize) {
    if array.as_var().is_some() {
        return;
    }
    let aux = format!("__hoisted_ptr_{counter}");
    *counter += 1;
    hoisted.push(Line::Statement {
        targets: vec![AssignmentTarget::Var {
            var: aux.clone(),
            is_mutable: false,
        }],
        value: Expression::Value(array.clone()),
        location: DUMMY_LOCATION,
    });
    *array = SimpleExpr::from(aux);
}

fn hoist_in_expr(expr: &mut Expression, hoisted: &mut Vec<Line>, counter: &mut usize) {
    for inner in expr.inner_exprs_mut() {
        hoist_in_expr(inner, hoisted, counter);
    }
    if let Expression::ArrayAccess { array, .. } = expr {
        hoist_base(array, hoisted, counter);
    }
}

fn hoist_in_lines(lines: &mut Vec<Line>, counter: &mut usize) {
    for mut line in std::mem::take(lines) {
        // Hoisted assignments go into `lines`, right before the line they came from.
        for expr in line.expressions_mut() {
            hoist_in_expr(expr, lines, counter);
        }
        if let Line::Statement { targets, .. } = &mut line {
            for target in targets {
                if let AssignmentTarget::ArrayAccess { array, .. } = target {
                    hoist_base(array, lines, counter);
                }
            }
        }
        for block in line.nested_blocks_mut() {
            hoist_in_lines(block, counter);
        }
        lines.push(line);
    }
}

fn check_no_unresolved_compile_time_constructs(program: &Program) -> Result<(), String> {
    let const_arrays = &program.const_arrays;
    for func in program.functions.values() {
        check_lines(&func.body, const_arrays).map_err(|e| format!("in function `{}`: {e}", func.name))?;
    }
    return Ok(());

    fn check_lines(lines: &[Line], const_arrays: &BTreeMap<String, ConstArrayValue>) -> Result<(), String> {
        for line in lines {
            if let Line::Statement { targets, .. } = line {
                for target in targets {
                    if let AssignmentTarget::ArrayAccess { array, .. } = target
                        && let Some(name) = array.as_var()
                        && const_arrays.contains_key(name)
                    {
                        return Err(format!("cannot assign to const array '{name}'"));
                    }
                }
            }
            for expr in line.expressions() {
                check_expr(expr, const_arrays)?;
            }
            for block in line.nested_blocks() {
                check_lines(block, const_arrays)?;
            }
        }
        Ok(())
    }

    fn check_expr(expr: &Expression, const_arrays: &BTreeMap<String, ConstArrayValue>) -> Result<(), String> {
        match expr {
            Expression::Len { array, .. } => {
                return Err(format!(
                    "`len({array})` could not be resolved at compile time (index must be a compile-time constant)"
                ));
            }
            Expression::Lambda { .. } => {
                return Err("Lambda expressions can only be used as arguments to match_range".to_string());
            }
            Expression::ArrayAccess { array, .. } => {
                if let Some(name) = array.as_var()
                    && const_arrays.contains_key(name)
                {
                    return Err(format!(
                        "access into const array '{name}' could not be resolved at compile time \
                         (index must be a compile-time constant)"
                    ));
                }
            }
            Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(name)))
                if const_arrays.contains_key(name) =>
            {
                return Err(format!("const array '{name}' cannot be used as a value"));
            }
            _ => {}
        }
        for inner in expr.inner_exprs() {
            check_expr(inner, const_arrays)?;
        }
        Ok(())
    }
}
