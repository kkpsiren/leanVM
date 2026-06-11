//! First compilation stage: full zkDSL -> intermediate zkDSL.

use crate::{ast_passes::*, intermediate_program::IntermediateProgram, lang::*};

mod legalize;
mod mut_to_ssa;
mod printer;
mod transforms;

pub use printer::intermediate_program_to_source;

pub fn compile_to_intermediate_program(mut program: Program) -> Result<IntermediateProgram, String> {
    check_program_scoping(&program)?;
    check_no_reserved_identifiers(&program)?;
    for (name, func) in &program.functions {
        check_no_dead_code(&func.body, name)?;
    }

    // `_` discard targets were named `@trash_N` by the parser; move them into
    // the reserved `__` namespace so they survive printing + re-parsing.
    for func in program.functions.values_mut() {
        transform_vars_in_lines(&mut func.body, &|var| match var.strip_prefix("@trash_") {
            Some(suffix) => VarTransform::Rename(format!("__trash_{suffix}")),
            None => VarTransform::Keep,
        });
    }

    transforms::compile_time_transform_in_program(&mut program)?;

    // Inlined functions have been spliced in; const functions have all been
    // specialized. Drop both.
    program
        .functions
        .retain(|_, func| !func.inlined && !func.has_const_arguments());

    transforms::check_no_loop_carried_mutables(&program)?;

    mut_to_ssa::eliminate_mutables(&mut program);
    legalize::legalize_program(&mut program)?;

    program.const_arrays.clear();

    // Constructing the intermediate AST validates the subset.
    IntermediateProgram::from_parsed(program)
}

/// Rejects user-defined identifiers starting with `__` (reserved for
/// compiler-generated names).
fn check_no_reserved_identifiers(program: &Program) -> Result<(), String> {
    fn check(name: &str) -> Result<(), String> {
        if name.starts_with("__") {
            return Err(format!(
                "identifier `{name}`: names starting with `__` are reserved for the compiler"
            ));
        }
        Ok(())
    }

    fn check_expr(expr: &Expression) -> Result<(), String> {
        match expr {
            Expression::Value(SimpleExpr::Memory(VarOrConstMallocAccess::Var(var))) => check(var)?,
            Expression::ArrayAccess { array, .. } => {
                if let Some(name) = array.as_var() {
                    check(name)?;
                }
            }
            Expression::Len { array, .. } => check(array)?,
            Expression::Lambda { param, .. } => check(param)?,
            Expression::FunctionCall { function_name, .. } => check(function_name)?,
            _ => {}
        }
        for inner in expr.inner_exprs() {
            check_expr(inner)?;
        }
        Ok(())
    }

    fn check_lines(lines: &[Line]) -> Result<(), String> {
        for line in lines {
            match line {
                Line::ForwardDeclaration { var, .. } => check(var)?,
                Line::Statement { targets, .. } => {
                    for target in targets {
                        match target {
                            AssignmentTarget::Var { var, .. } => check(var)?,
                            AssignmentTarget::ArrayAccess { array, .. } => {
                                if let Some(name) = array.as_var() {
                                    check(name)?;
                                }
                            }
                        }
                    }
                }
                Line::ForLoop { iterator, .. } => check(iterator)?,
                _ => {}
            }
            for expr in line.expressions() {
                check_expr(expr)?;
            }
            for block in line.nested_blocks() {
                check_lines(block)?;
            }
        }
        Ok(())
    }

    for name in program.const_arrays.keys() {
        check(name)?;
    }
    for (name, func) in &program.functions {
        check(name)?;
        for arg in &func.arguments {
            check(&arg.name)?;
        }
        check_lines(&func.body)?;
    }
    Ok(())
}
