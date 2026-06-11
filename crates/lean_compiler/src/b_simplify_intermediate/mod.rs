//! Second compilation stage (front): intermediate zkDSL -> `SimpleProgram`.
//!
//! Purely structural lowering (expression flattening, `range` loops ->
//! recursive functions, asserts -> range checks, precompile/hint resolution),
//! with no symbolic rewriting — the hard rewriting all happened in stage 1.

use crate::{
    intermediate_program::{
        IntermediateExpr, IntermediateFunction, IntermediateLine, IntermediateProgram, IntermediateTarget,
        find_variable_usage, vars_in_expression,
    },
    lang::*,
};
use backend::*;
use lean_vm::{
    ALL_POSEIDON16_NAMES, Boolean, BooleanExpr, CustomHint, ExtensionOpMode, FunctionName,
    POSEIDON16_HARDCODED_LEFT_NAME, POSEIDON16_PERMUTE_HALF_HARDCODED_LEFT_NAME, POSEIDON16_PERMUTE_HALF_NAME,
    POSEIDON16_PERMUTE_NAME, POSEIDON16_QUARTER_HARDCODED_LEFT_NAME, POSEIDON16_QUARTER_NAME, PrecompileArgs,
    PrecompileCompTimeArgs, SourceLocation,
};
use std::{
    collections::{BTreeMap, BTreeSet},
    fmt::{Display, Formatter},
};

mod post_optimization;

#[derive(Debug, Clone)]
pub struct SimpleProgram {
    pub functions: BTreeMap<FunctionName, SimpleFunction>,
}

#[derive(Debug, Clone)]
pub struct SimpleFunction {
    pub name: String,
    pub arguments: Vec<Var>,
    pub n_returned_vars: usize,
    pub instructions: Vec<SimpleLine>,
}

pub type SimplePrecompile = PrecompileArgs<SimpleExpr, ConstExpression>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum SimpleLine {
    Match {
        value: SimpleExpr,
        arms: Vec<Vec<Self>>,
        offset: usize, // first pattern value (arms are for offset, offset+1, ...)
    },
    ForwardDeclaration {
        var: Var,
    },
    Assignment {
        // `var = arg0 op arg1`
        var: SimpleExpr,
        op: MathOperation, // add / sub / div / mul
        arg0: SimpleExpr,
        arg1: SimpleExpr,
    },
    RawAccess {
        res: SimpleExpr,
        index: SimpleExpr,
        shift: ConstExpression,
    }, // res = memory[index + shift]
    IfNotZero {
        condition: SimpleExpr,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
        location: SourceLocation,
    },
    FunctionCall {
        function_name: String,
        args: Vec<SimpleExpr>,
        return_data: Vec<Var>,
        location: SourceLocation,
    },
    FunctionRet {
        return_data: Vec<SimpleExpr>,
    },
    Precompile(SimplePrecompile),
    Panic {
        message: Option<String>,
    },
    CustomHint(CustomHint, Vec<SimpleExpr>),
    /// Write the next witness entry for `name` into the buffer at `destination`.
    HintWitness {
        destination: SimpleExpr,
        name: String,
    },
    Print {
        line_info: String,
        content: Vec<SimpleExpr>,
    },
    HintMAlloc {
        var: Var,
        size: SimpleExpr,
    },
    ConstMalloc {
        var: Var,
        size: ConstExpression,
        label: ConstMallocLabel,
    },
    /// noop, debug purpose only
    LocationReport {
        location: SourceLocation,
    },
    DebugAssert {
        expr: BooleanExpr<SimpleExpr>,
        location: SourceLocation,
        // Soundness: a `RangeCheck` is preceded by a less-than hint that checks
        // at runtime both that the inequality holds and that the bound is
        // <= 2^MIN_LOG_MEMORY_SIZE (cf. "Range checks", minimal_zkVM.pdf §2.6.3).
        preceds_runtime_inequality: bool,
    },
    /// Runtime assertion `left == right`. Distinct from `Assignment` so dead-store
    /// analysis cannot drop it.
    AssertEq {
        left: SimpleExpr,
        right: SimpleExpr,
        location: SourceLocation,
    },
    RangeCheck {
        val: SimpleExpr,
        bound: SimpleExpr,
    },
}

impl SimpleLine {
    pub fn equality(arg0: impl Into<SimpleExpr>, arg1: impl Into<SimpleExpr>) -> Self {
        SimpleLine::Assignment {
            var: arg0.into(),
            op: MathOperation::Add,
            arg0: arg1.into(),
            arg1: SimpleExpr::zero(),
        }
    }

    /// Mutable references to all nested blocks (match arms, if branches).
    pub fn nested_blocks_mut(&mut self) -> Vec<&mut Vec<SimpleLine>> {
        match self {
            Self::Match { arms, .. } => arms.iter_mut().collect(),
            Self::IfNotZero {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Self::ForwardDeclaration { .. }
            | Self::Assignment { .. }
            | Self::RawAccess { .. }
            | Self::FunctionCall { .. }
            | Self::FunctionRet { .. }
            | Self::Precompile(..)
            | Self::Panic { .. }
            | Self::CustomHint(..)
            | Self::HintWitness { .. }
            | Self::Print { .. }
            | Self::HintMAlloc { .. }
            | Self::ConstMalloc { .. }
            | Self::LocationReport { .. }
            | Self::DebugAssert { .. }
            | Self::AssertEq { .. }
            | Self::RangeCheck { .. } => vec![],
        }
    }

    pub fn nested_blocks(&self) -> Vec<&Vec<SimpleLine>> {
        match self {
            Self::Match { arms, .. } => arms.iter().collect(),
            Self::IfNotZero {
                then_branch,
                else_branch,
                ..
            } => vec![then_branch, else_branch],
            Self::ForwardDeclaration { .. }
            | Self::Assignment { .. }
            | Self::RawAccess { .. }
            | Self::FunctionCall { .. }
            | Self::FunctionRet { .. }
            | Self::Precompile(..)
            | Self::Panic { .. }
            | Self::CustomHint(..)
            | Self::HintWitness { .. }
            | Self::Print { .. }
            | Self::HintMAlloc { .. }
            | Self::ConstMalloc { .. }
            | Self::LocationReport { .. }
            | Self::DebugAssert { .. }
            | Self::AssertEq { .. }
            | Self::RangeCheck { .. } => vec![],
        }
    }

    /// All `SimpleExpr` operands read by this instruction (excludes assignment targets).
    pub(crate) fn operand_exprs(&self) -> Vec<&SimpleExpr> {
        match self {
            Self::Assignment { arg0, arg1, .. } => {
                vec![arg0, arg1]
            }
            Self::RawAccess { res, index, .. } => vec![res, index],
            Self::RangeCheck { val, bound } => vec![val, bound],
            Self::Match { value, .. } => vec![value],
            Self::IfNotZero { condition, .. } => vec![condition],
            Self::HintMAlloc { size, .. } => vec![size],
            Self::Precompile(precompile) => precompile.operand_exprs().to_vec(),
            Self::FunctionCall { args, .. } | Self::CustomHint(_, args) => args.iter().collect(),
            Self::FunctionRet { return_data } => return_data.iter().collect(),
            Self::Print { content, .. } => content.iter().collect(),
            Self::DebugAssert { expr, .. } => vec![&expr.left, &expr.right],
            Self::AssertEq { left, right, .. } => vec![left, right],
            Self::HintWitness { destination, .. } => vec![destination],
            Self::ForwardDeclaration { .. }
            | Self::ConstMalloc { .. }
            | Self::LocationReport { .. }
            | Self::Panic { .. } => vec![],
        }
    }

    pub(crate) fn operand_exprs_mut(&mut self) -> Vec<&mut SimpleExpr> {
        match self {
            Self::Assignment { arg0, arg1, .. } => vec![arg0, arg1],
            Self::RawAccess { res, index, .. } => vec![res, index],
            Self::RangeCheck { val, bound } => vec![val, bound],
            Self::Match { value, .. } => vec![value],
            Self::IfNotZero { condition, .. } => vec![condition],
            Self::HintMAlloc { size, .. } => vec![size],
            Self::Precompile(p) => p.operand_exprs_mut().into_iter().collect(),
            Self::FunctionCall { args, .. } | Self::CustomHint(_, args) => args.iter_mut().collect(),
            Self::FunctionRet { return_data } => return_data.iter_mut().collect(),
            Self::Print { content, .. } => content.iter_mut().collect(),
            Self::DebugAssert { expr, .. } => vec![&mut expr.left, &mut expr.right],
            Self::AssertEq { left, right, .. } => vec![left, right],
            Self::HintWitness { destination, .. } => vec![destination],
            Self::ForwardDeclaration { .. }
            | Self::ConstMalloc { .. }
            | Self::LocationReport { .. }
            | Self::Panic { .. } => vec![],
        }
    }
}

pub fn simplify_intermediate_program(program: &IntermediateProgram) -> Result<SimpleProgram, String> {
    let mut new_functions = BTreeMap::new();
    let mut counters = Counters::default();
    let mut const_malloc = ConstMalloc::default();
    let ctx = SimplifyContext {
        functions: &program.functions,
    };
    for (name, func) in &program.functions {
        let mut array_manager = ArrayManager::default();
        // Arguments count as assigned, to detect illegal reassignment.
        let mut assigned: BTreeSet<Var> = func.arguments.iter().cloned().collect();

        let mut state = SimplifyState {
            counters: &mut counters,
            array_manager: &mut array_manager,
            assigned: &mut assigned,
        };
        let simplified_instructions = simplify_lines(
            &ctx,
            &mut state,
            &mut const_malloc,
            &mut new_functions,
            func.n_returned_vars,
            &func.body,
            false,
        )?;
        let simplified_function = SimpleFunction {
            name: name.clone(),
            arguments: func.arguments.clone(),
            n_returned_vars: func.n_returned_vars,
            instructions: simplified_instructions,
        };
        check_block_always_returns(name, &simplified_function.instructions)?;
        new_functions.insert(name.clone(), simplified_function);
        const_malloc.map.clear();
    }

    let mut simple_program = SimpleProgram {
        functions: new_functions,
    };
    post_optimization::propagate_copies(&mut simple_program);
    Ok(simple_program)
}

fn check_block_always_returns(function_name: &str, instructions: &[SimpleLine]) -> Result<(), String> {
    if let Some(last_instruction) = instructions.last() {
        if matches!(
            last_instruction,
            SimpleLine::FunctionRet { return_data: _ } | SimpleLine::Panic { .. }
        ) {
            return Ok(());
        }
        let inner_blocks = last_instruction.nested_blocks();
        if !inner_blocks.is_empty() {
            for block in inner_blocks {
                check_block_always_returns(function_name, block)?;
            }
            return Ok(());
        }
    }
    Err(format!("Cannot prove that function always returns: {function_name}"))
}

/// True if the block leaves the enclosing function (return/panic) on every path
/// through its last statement. Mirrors `ast_passes::ends_with_early_exit`.
fn ends_with_early_exit(block: &[IntermediateLine]) -> bool {
    match block.last() {
        Some(IntermediateLine::Panic { .. }) | Some(IntermediateLine::FunctionRet { .. }) => true,
        // A loop may run zero times, so a trailing loop never guarantees an exit.
        Some(IntermediateLine::ForLoop { .. }) | None => false,
        Some(IntermediateLine::IfCondition {
            then_branch,
            else_branch,
            ..
        }) => ends_with_early_exit(then_branch) && ends_with_early_exit(else_branch),
        Some(IntermediateLine::Match { arms, .. }) => {
            !arms.is_empty() && arms.iter().all(|(_, arm)| ends_with_early_exit(arm))
        }
        Some(_) => false,
    }
}

#[derive(Debug, Clone, Default)]
struct Counters {
    aux_vars: Counter,
    loops: Counter,
}

impl Counters {
    fn aux_var(&mut self) -> Var {
        format!("@aux_var_{}", self.aux_vars.get_next())
    }
}

struct SimplifyContext<'a> {
    functions: &'a BTreeMap<FunctionName, IntermediateFunction>,
}

struct SimplifyState<'a> {
    counters: &'a mut Counters,
    array_manager: &'a mut ArrayManager,
    /// Already-assigned (immutable) variables, to detect illegal reassignment.
    assigned: &'a mut BTreeSet<Var>,
}

#[derive(Debug, Clone, Default)]
struct ArrayManager {
    counter: usize,
    aux_vars: BTreeMap<(Var, IntermediateExpr), Var>, // (array, index) -> aux_var
    valid: BTreeSet<Var>,                             // currently-valid aux vars
}

#[derive(Debug, Clone, Default)]
pub struct ConstMalloc {
    counter: usize,
    map: BTreeMap<Var, ConstMallocLabel>,
}

impl ArrayManager {
    fn get_aux_var(&mut self, array: &Var, index: &IntermediateExpr) -> Var {
        if let Some(var) = self.aux_vars.get(&(array.clone(), index.clone())) {
            return var.clone();
        }
        let new_var = format!("@arr_aux_{}", self.counter);
        self.counter += 1;
        self.aux_vars.insert((array.clone(), index.clone()), new_var.clone());
        new_var
    }
}

#[allow(clippy::too_many_arguments)]
fn simplify_lines(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &mut ConstMalloc,
    new_functions: &mut BTreeMap<String, SimpleFunction>,
    n_returned_vars: usize,
    lines: &[IntermediateLine],
    in_a_loop: bool,
) -> Result<Vec<SimpleLine>, String> {
    let mut res = Vec::new();
    for line in lines {
        match line {
            IntermediateLine::Declaration { var } => {
                res.push(SimpleLine::ForwardDeclaration { var: var.clone() });
            }
            IntermediateLine::Match { value, arms, .. } => {
                let first_pattern = arms.first().map(|(p, _)| *p).unwrap_or(0);
                for (i, (pattern, _)) in arms.iter().enumerate() {
                    if *pattern != first_pattern + i {
                        return Err(format!(
                            "match patterns must be consecutive, expected {} but got {}",
                            first_pattern + i,
                            pattern
                        ));
                    }
                }

                let simple_value = simplify_expr(ctx, state, const_malloc, value, &mut res)?;

                // Each arm starts from the same pre-match state (only one runs).
                let assigned_snapshot = state.assigned.clone();
                let array_manager_snapshot = state.array_manager.clone();
                let const_malloc_snapshot = const_malloc.map.clone();

                // A var assigned in a fall-through arm is assigned after the match
                // (same frame slot), so a later reassignment is rejected.
                let mut assigned_after = assigned_snapshot.clone();

                let mut simple_arms = vec![];
                for (_, statements) in arms.iter() {
                    *state.assigned = assigned_snapshot.clone();
                    *state.array_manager = array_manager_snapshot.clone();
                    const_malloc.map = const_malloc_snapshot.clone();

                    let arm_simplified = simplify_lines(
                        ctx,
                        state,
                        const_malloc,
                        new_functions,
                        n_returned_vars,
                        statements,
                        in_a_loop,
                    )?;
                    simple_arms.push(arm_simplified);
                    if !ends_with_early_exit(statements) {
                        assigned_after.extend(state.assigned.iter().cloned());
                    }
                }

                // Restore pre-match state; arm-local `Array(..)` must not leak out.
                *state.assigned = assigned_after;
                *state.array_manager = array_manager_snapshot;
                const_malloc.map = const_malloc_snapshot;

                res.push(SimpleLine::Match {
                    value: simple_value,
                    arms: simple_arms,
                    offset: first_pattern,
                });
            }
            IntermediateLine::Statement {
                targets,
                value,
                location,
            } => {
                let get_target_var_name = |state: &mut SimplifyState<'_>, var: &Var| -> Result<Var, String> {
                    if !state.assigned.insert(var.clone()) {
                        return Err(format!(
                            "Cannot reassign immutable variable '{var}' (use 'assert {var} == <value>;' to check equality)"
                        ));
                    }
                    Ok(var.clone())
                };

                match value {
                    IntermediateExpr::HintWitness { name: hint_name, ptr } => {
                        if !targets.is_empty() {
                            return Err(format!("hint_witness has no return value, at {location}"));
                        }
                        let simplified_ptr = simplify_expr(ctx, state, const_malloc, ptr, &mut res)?;
                        res.push(SimpleLine::HintWitness {
                            destination: simplified_ptr,
                            name: hint_name.clone(),
                        });
                        continue;
                    }
                    IntermediateExpr::FunctionCall { function, args, .. } => {
                        if function == "Array" {
                            if args.len() != 1 {
                                return Err(format!(
                                    "Array expects exactly 1 argument, got {}, at {location}",
                                    args.len()
                                ));
                            }
                            if targets.len() != 1 {
                                return Err(format!(
                                    "Array expects exactly 1 return target, got {}, at {location}",
                                    targets.len()
                                ));
                            }
                            match &targets[0] {
                                IntermediateTarget::Var(var) => {
                                    let target_var = get_target_var_name(state, var)?;
                                    let simplified_size = simplify_expr(ctx, state, const_malloc, &args[0], &mut res)?;
                                    match simplified_size {
                                        SimpleExpr::Constant(const_size) => {
                                            let label = const_malloc.counter;
                                            const_malloc.counter += 1;
                                            const_malloc.map.insert(target_var.clone(), label);
                                            res.push(SimpleLine::ConstMalloc {
                                                var: target_var,
                                                size: const_size,
                                                label,
                                            });
                                        }
                                        _ => {
                                            res.push(SimpleLine::HintMAlloc {
                                                var: target_var,
                                                size: simplified_size,
                                            });
                                        }
                                    }
                                }
                                IntermediateTarget::ArrayAccess { .. } => {
                                    return Err(format!(
                                        "Array does not support array access as return target, at {location}"
                                    ));
                                }
                            }
                            continue;
                        }

                        if function == "print" {
                            if !targets.is_empty() {
                                return Err(format!("print should not return values, at {location}"));
                            }
                            let simplified_content = args
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;
                            res.push(SimpleLine::Print {
                                line_info: format!("line {}", location.line_number),
                                content: simplified_content,
                            });
                            continue;
                        }

                        // extension_op: func(ptr_a, ptr_b, ptr_res[, length])
                        if let Some(mode) = ExtensionOpMode::from_name(function) {
                            if !targets.is_empty() {
                                return Err(format!("Precompile {function} should not return values, at {location}"));
                            }
                            if args.len() != 3 && args.len() != 4 {
                                return Err(format!(
                                    "Precompile {function} expects 3 or 4 arguments (a, b, result[, length]), got {}, at {location}",
                                    args.len()
                                ));
                            }
                            let simplified_args = args[..3]
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;

                            let size = if args.len() == 4 {
                                simplify_expr(ctx, state, const_malloc, &args[3], &mut res)?
                                    .as_constant()
                                    .ok_or_else(|| {
                                        format!(
                                            "Precompile {function}: length argument must be a compile-time constant, at {location}"
                                        )
                                    })?
                            } else {
                                ConstExpression::one()
                            };
                            res.push(SimpleLine::Precompile(PrecompileArgs {
                                arg_0: simplified_args[0].clone(),
                                arg_1: simplified_args[1].clone(),
                                res: simplified_args[2].clone(),
                                data: PrecompileCompTimeArgs::ExtensionOp { size, mode },
                            }));
                            continue;
                        }

                        // poseidon16 (5 variants)
                        if ALL_POSEIDON16_NAMES.contains(&function.as_str()) {
                            if !targets.is_empty() {
                                return Err(format!("Precompile {function} should not return values, at {location}"));
                            }
                            let permute = [
                                POSEIDON16_PERMUTE_NAME,
                                POSEIDON16_PERMUTE_HALF_NAME,
                                POSEIDON16_PERMUTE_HALF_HARDCODED_LEFT_NAME,
                            ]
                            .contains(&function.as_str());
                            let half_output = [
                                POSEIDON16_QUARTER_NAME,
                                POSEIDON16_QUARTER_HARDCODED_LEFT_NAME,
                                POSEIDON16_PERMUTE_HALF_NAME,
                                POSEIDON16_PERMUTE_HALF_HARDCODED_LEFT_NAME,
                            ]
                            .contains(&function.as_str());
                            let is_hardcoded_left = [
                                POSEIDON16_HARDCODED_LEFT_NAME,
                                POSEIDON16_QUARTER_HARDCODED_LEFT_NAME,
                                POSEIDON16_PERMUTE_HALF_HARDCODED_LEFT_NAME,
                            ]
                            .contains(&function.as_str());
                            let expected_args = if is_hardcoded_left { 4 } else { 3 };
                            if args.len() != expected_args {
                                let signature = if is_hardcoded_left {
                                    "(ptr_a, ptr_b, ptr_res, offset)"
                                } else {
                                    "(ptr_a, ptr_b, ptr_res)"
                                };
                                return Err(format!(
                                    "Precompile {function} expects {expected_args} arguments {signature}, got {}, at {location}",
                                    args.len()
                                ));
                            }
                            let simplified_args = args
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;
                            let hardcoded_offset_left = if is_hardcoded_left {
                                Some(simplified_args[3].as_constant().ok_or_else(|| {
                                    format!(
                                        "{function}: offset argument must be a compile-time constant, at {location}"
                                    )
                                })?)
                            } else {
                                None
                            };
                            res.push(SimpleLine::Precompile(PrecompileArgs {
                                arg_0: simplified_args[0].clone(),
                                arg_1: simplified_args[1].clone(),
                                res: simplified_args[2].clone(),
                                data: PrecompileCompTimeArgs::Poseidon16 {
                                    half_output,
                                    hardcoded_offset_left,
                                    permute,
                                },
                            }));
                            continue;
                        }

                        if let Some(hint) = CustomHint::find_by_name(function) {
                            if !targets.is_empty() {
                                return Err(format!(
                                    "Custom hint {function} should not return values, at {location}"
                                ));
                            }
                            if args.len() != hint.n_args() {
                                return Err(format!(
                                    "Custom hint {function}: invalid number of arguments, at {location}"
                                ));
                            }
                            let simplified_args = args
                                .iter()
                                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                                .collect::<Result<Vec<_>, _>>()?;
                            res.push(SimpleLine::CustomHint(hint, simplified_args));
                            continue;
                        }

                        // Regular function call.
                        let callee = ctx
                            .functions
                            .get(function)
                            .ok_or_else(|| format!("Function used but not defined: {function}, at {location}"))?;
                        if targets.len() != callee.n_returned_vars {
                            return Err(format!(
                                "Expected {} returned vars (and not {}) in call to {function}, at {location}",
                                callee.n_returned_vars,
                                targets.len()
                            ));
                        }
                        if args.len() != callee.arguments.len() {
                            return Err(format!(
                                "Expected {} arguments (and not {}) in call to {function}, at {location}",
                                callee.arguments.len(),
                                args.len()
                            ));
                        }

                        let simplified_args = args
                            .iter()
                            .map(|arg| simplify_expr(ctx, state, const_malloc, arg, &mut res))
                            .collect::<Result<Vec<_>, _>>()?;

                        let mut temp_vars = Vec::new();
                        let mut array_targets: Vec<(usize, Var, IntermediateExpr)> = Vec::new();

                        for (i, target) in targets.iter().enumerate() {
                            match target {
                                IntermediateTarget::Var(var) => {
                                    temp_vars.push(get_target_var_name(state, var)?);
                                }
                                IntermediateTarget::ArrayAccess { array, index } => {
                                    temp_vars.push(state.counters.aux_var());
                                    array_targets.push((i, array.clone(), index.clone()));
                                }
                            }
                        }

                        res.push(SimpleLine::FunctionCall {
                            function_name: function.clone(),
                            args: simplified_args,
                            return_data: temp_vars.clone(),
                            location: *location,
                        });

                        // DEREF each array-access target's temp into its element.
                        for (i, array, index) in array_targets {
                            let simplified_index = simplify_expr(ctx, state, const_malloc, &index, &mut res)?;
                            let simplified_value = VarOrConstMallocAccess::Var(temp_vars[i].clone()).into();
                            handle_array_assignment(
                                state,
                                const_malloc,
                                &mut res,
                                &array,
                                &simplified_index,
                                ArrayAccessType::ArrayIsAssigned(simplified_value),
                            );
                        }
                    }
                    _ => {
                        assert!(targets.len() == 1, "Non-function call must have exactly one target");

                        match &targets[0] {
                            IntermediateTarget::Var(var) => match value {
                                IntermediateExpr::Var(_) | IntermediateExpr::Constant(_) => {
                                    let simplified_val = simplify_expr(ctx, state, const_malloc, value, &mut res)?;
                                    let target_var = get_target_var_name(state, var)?;
                                    res.push(SimpleLine::equality(target_var, simplified_val));
                                }
                                IntermediateExpr::ArrayAccess { array, index } => {
                                    // Direct deref into the target (no aux-var caching).
                                    let simplified_index = simplify_expr(ctx, state, const_malloc, index, &mut res)?;
                                    let target_var = get_target_var_name(state, var)?;
                                    handle_array_assignment(
                                        state,
                                        const_malloc,
                                        &mut res,
                                        array,
                                        &simplified_index,
                                        ArrayAccessType::VarIsAssigned(target_var),
                                    );
                                }
                                IntermediateExpr::Math { op, left, right } => {
                                    let arg0 = simplify_expr(ctx, state, const_malloc, left, &mut res)?;
                                    let arg1 = simplify_expr(ctx, state, const_malloc, right, &mut res)?;
                                    let target_var = get_target_var_name(state, var)?;
                                    res.push(SimpleLine::Assignment {
                                        var: target_var.into(),
                                        op: (*op).into(),
                                        arg0,
                                        arg1,
                                    });
                                }
                                IntermediateExpr::FunctionCall { .. } | IntermediateExpr::HintWitness { .. } => {
                                    unreachable!("handled above")
                                }
                            },
                            IntermediateTarget::ArrayAccess { array, index } => {
                                let simplified_index = simplify_expr(ctx, state, const_malloc, index, &mut res)?;

                                // Direct math assignment into a const_malloc slot at a constant index.
                                if let SimpleExpr::Constant(offset) = &simplified_index
                                    && let Some(&label) = const_malloc.map.get(array)
                                    && let IntermediateExpr::Math { op, left, right } = value
                                {
                                    let var = VarOrConstMallocAccess::ConstMallocAccess {
                                        malloc_label: label,
                                        offset: offset.clone(),
                                    };
                                    let arg0 = simplify_expr(ctx, state, const_malloc, left, &mut res)?;
                                    let arg1 = simplify_expr(ctx, state, const_malloc, right, &mut res)?;
                                    res.push(SimpleLine::Assignment {
                                        var: var.into(),
                                        op: (*op).into(),
                                        arg0,
                                        arg1,
                                    });
                                } else {
                                    let simplified_value = simplify_expr(ctx, state, const_malloc, value, &mut res)?;
                                    handle_array_assignment(
                                        state,
                                        const_malloc,
                                        &mut res,
                                        array,
                                        &simplified_index,
                                        ArrayAccessType::ArrayIsAssigned(simplified_value),
                                    );
                                }
                            }
                        }
                    }
                }
            }
            IntermediateLine::Assert {
                boolean,
                debug,
                location,
            } => {
                let left = simplify_expr(ctx, state, const_malloc, &boolean.left, &mut res)?;
                let right = simplify_expr(ctx, state, const_malloc, &boolean.right, &mut res)?;
                if *debug {
                    res.push(SimpleLine::DebugAssert {
                        expr: BooleanExpr {
                            left,
                            right,
                            kind: boolean.kind,
                        },
                        location: *location,
                        preceds_runtime_inequality: false,
                    });
                } else {
                    match boolean.kind {
                        Boolean::Different => {
                            let diff_var = state.counters.aux_var();
                            res.push(SimpleLine::Assignment {
                                var: diff_var.clone().into(),
                                op: MathOperation::Sub,
                                arg0: left,
                                arg1: right,
                            });
                            res.push(SimpleLine::IfNotZero {
                                condition: diff_var.into(),
                                then_branch: vec![],
                                else_branch: vec![SimpleLine::Panic { message: None }],
                                location: *location,
                            });
                        }
                        Boolean::Equal => {
                            // Both constants: evaluate at compile time.
                            if let (SimpleExpr::Constant(left_const), SimpleExpr::Constant(right_const)) =
                                (&left, &right)
                                && let (Some(left_val), Some(right_val)) =
                                    (left_const.naive_eval(), right_const.naive_eval())
                            {
                                if left_val == right_val {
                                    continue;
                                } else {
                                    return Err(format!(
                                        "Compile-time assertion failed: {} != {} ({})",
                                        left_val.to_usize(),
                                        right_val.to_usize(),
                                        location
                                    ));
                                }
                            }
                            if !matches!(&left, SimpleExpr::Memory(_)) && !matches!(&right, SimpleExpr::Memory(_)) {
                                return Err(format!("Unsupported equality assertion: {left:?}, {right:?}"));
                            }
                            res.push(SimpleLine::AssertEq {
                                left,
                                right,
                                location: *location,
                            });
                        }
                        Boolean::LessThan => {
                            // `left < right` is `left <= right - 1`.
                            let bound_minus_one = state.counters.aux_var();
                            res.push(SimpleLine::Assignment {
                                var: bound_minus_one.clone().into(),
                                op: MathOperation::Sub,
                                arg0: right,
                                arg1: SimpleExpr::one(),
                            });

                            res.push(SimpleLine::DebugAssert {
                                expr: BooleanExpr {
                                    kind: Boolean::LessOrEqual,
                                    left: left.clone(),
                                    right: bound_minus_one.clone().into(),
                                },
                                location: *location,
                                preceds_runtime_inequality: true,
                            });

                            res.push(SimpleLine::RangeCheck {
                                val: left,
                                bound: bound_minus_one.into(),
                            });
                        }
                        Boolean::LessOrEqual => {
                            res.push(SimpleLine::DebugAssert {
                                expr: BooleanExpr {
                                    kind: Boolean::LessOrEqual,
                                    left: left.clone(),
                                    right: right.clone(),
                                },
                                location: *location,
                                preceds_runtime_inequality: true,
                            });

                            res.push(SimpleLine::RangeCheck {
                                val: left,
                                bound: right,
                            });
                        }
                    }
                }
            }
            IntermediateLine::IfCondition {
                condition,
                then_branch,
                else_branch,
                location,
            } => {
                // `if a == b {X} else {Y}` becomes `if a != b {Y} else {X}`.
                let (left, right, then_branch, else_branch) = match condition.kind {
                    Boolean::Equal => (&condition.left, &condition.right, else_branch, then_branch), // swapped
                    Boolean::Different => (&condition.left, &condition.right, then_branch, else_branch),
                    Boolean::LessThan | Boolean::LessOrEqual => {
                        return Err(format!("if conditions only support `==` and `!=`, at {location}"));
                    }
                };

                let left_simplified = simplify_expr(ctx, state, const_malloc, left, &mut res)?;
                let right_simplified = simplify_expr(ctx, state, const_malloc, right, &mut res)?;

                let diff_var = state.counters.aux_var();
                res.push(SimpleLine::Assignment {
                    var: diff_var.clone().into(),
                    op: MathOperation::Sub,
                    arg0: left_simplified,
                    arg1: right_simplified,
                });
                let condition_simplified: SimpleExpr = diff_var.into();

                let const_malloc_snapshot = const_malloc.map.clone();

                let mut array_manager_then = state.array_manager.clone();
                let mut assigned_then = state.assigned.clone();
                let mut state_then = SimplifyState {
                    counters: state.counters,
                    array_manager: &mut array_manager_then,
                    assigned: &mut assigned_then,
                };
                let then_branch_simplified = simplify_lines(
                    ctx,
                    &mut state_then,
                    const_malloc,
                    new_functions,
                    n_returned_vars,
                    then_branch,
                    in_a_loop,
                )?;

                let mut array_manager_else = array_manager_then.clone();
                array_manager_else.valid = state.array_manager.valid.clone(); // crucial: drop accesses added in the if branch

                const_malloc.map = const_malloc_snapshot.clone();
                let mut assigned_else = state.assigned.clone();
                let mut state_else = SimplifyState {
                    counters: state.counters,
                    array_manager: &mut array_manager_else,
                    assigned: &mut assigned_else,
                };
                let else_branch_simplified = simplify_lines(
                    ctx,
                    &mut state_else,
                    const_malloc,
                    new_functions,
                    n_returned_vars,
                    else_branch,
                    in_a_loop,
                )?;

                // Branch-local `Array(..)` must not leak past the branch.
                const_malloc.map = const_malloc_snapshot;
                // A var assigned in a fall-through branch is assigned afterwards
                // (same frame slot), so a later reassignment is rejected.
                if !ends_with_early_exit(then_branch) {
                    state.assigned.extend(assigned_then);
                }
                if !ends_with_early_exit(else_branch) {
                    state.assigned.extend(assigned_else);
                }

                *state.array_manager = array_manager_else.clone();
                // keep only accesses valid in both branches
                state.array_manager.valid = state
                    .array_manager
                    .valid
                    .intersection(&array_manager_then.valid)
                    .cloned()
                    .collect();

                res.push(SimpleLine::IfNotZero {
                    condition: condition_simplified,
                    then_branch: then_branch_simplified,
                    else_branch: else_branch_simplified,
                    location: *location,
                });
            }
            IntermediateLine::ForLoop {
                iterator,
                start,
                end,
                body,
                parallel,
                location,
            } => {
                let mut loop_const_malloc = ConstMalloc {
                    counter: const_malloc.counter,
                    ..ConstMalloc::default()
                };
                let valid_aux_vars_in_array_manager_before = state.array_manager.valid.clone();
                state.array_manager.valid.clear();

                // The body becomes its own function, so its assignments don't reach outer scope.
                let assigned_before = std::mem::take(state.assigned);
                let simplified_body = simplify_lines(ctx, state, &mut loop_const_malloc, new_functions, 0, body, true)?;
                *state.assigned = assigned_before;

                const_malloc.counter = loop_const_malloc.counter;
                state.array_manager.valid = valid_aux_vars_in_array_manager_before; // restore the valid aux vars

                let loop_prefix = if *parallel { "@parallel_loop" } else { "@loop" };
                let func_name = format!("{}_{}_{}", loop_prefix, state.counters.loops.get_next(), location);

                // Variables used in the loop (body + bounds) but defined outside.
                let (_, mut external_vars) = find_variable_usage(body);
                for expr in [start, end] {
                    for var in vars_in_expression(expr) {
                        external_vars.insert(var);
                    }
                }
                external_vars.remove(iterator); // the iterator is loop-internal

                let mut external_vars: Vec<_> = external_vars.into_iter().collect();

                let start_simplified = simplify_expr(ctx, state, const_malloc, start, &mut res)?;
                let mut end_simplified = simplify_expr(ctx, state, const_malloc, end, &mut res)?;
                if let SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset }) =
                    end_simplified.clone()
                {
                    // const_malloc accesses don't work inside recursive loops; copy to an aux var.
                    let aux_end_var = state.counters.aux_var();
                    res.push(SimpleLine::equality(
                        aux_end_var.clone(),
                        VarOrConstMallocAccess::ConstMallocAccess { malloc_label, offset },
                    ));
                    end_simplified = VarOrConstMallocAccess::Var(aux_end_var).into();
                }

                // A non-trivial bound simplified to an aux var must be passed in too.
                for (simplified, original) in [(&start_simplified, start), (&end_simplified, end)] {
                    if !matches!(original, IntermediateExpr::Var(_) | IntermediateExpr::Constant(_))
                        && let SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) = simplified
                    {
                        external_vars.push(var.clone());
                    }
                }

                res.push(SimpleLine::DebugAssert {
                    expr: BooleanExpr {
                        kind: Boolean::LessOrEqual,
                        left: start_simplified.clone(),
                        right: end_simplified.clone(),
                    },
                    location: *location,
                    preceds_runtime_inequality: false,
                });

                let mut func_args = vec![iterator.clone()];
                func_args.extend(external_vars.clone());

                let recursive_func = create_recursive_function(
                    func_name.clone(),
                    *location,
                    func_args,
                    iterator.clone(),
                    end_simplified,
                    simplified_body,
                    &external_vars,
                );
                new_functions.insert(func_name.clone(), recursive_func);

                // Replace the loop with the initial call.
                let mut call_args = vec![start_simplified];
                call_args.extend(external_vars.iter().map(|v| v.clone().into()));

                res.push(SimpleLine::FunctionCall {
                    function_name: func_name,
                    args: call_args,
                    return_data: vec![],
                    location: *location,
                });
            }
            IntermediateLine::FunctionRet { return_data } => {
                if in_a_loop {
                    return Err("Function return inside a loop is not currently supported".to_string());
                }
                if return_data.len() != n_returned_vars {
                    return Err(format!(
                        "Wrong number of return values in return statement; expected {n_returned_vars} but got {}",
                        return_data.len()
                    ));
                }
                let simplified_return_data = return_data
                    .iter()
                    .map(|ret| simplify_expr(ctx, state, const_malloc, ret, &mut res))
                    .collect::<Result<Vec<_>, _>>()?;
                res.push(SimpleLine::FunctionRet {
                    return_data: simplified_return_data,
                });
            }
            IntermediateLine::Panic { message } => {
                res.push(SimpleLine::Panic {
                    message: message.clone(),
                });
            }
            IntermediateLine::LocationReport { location } => {
                res.push(SimpleLine::LocationReport { location: *location });
            }
        }
    }

    Ok(res)
}

fn simplify_expr(
    ctx: &SimplifyContext<'_>,
    state: &mut SimplifyState<'_>,
    const_malloc: &ConstMalloc,
    expr: &IntermediateExpr,
    lines: &mut Vec<SimpleLine>,
) -> Result<SimpleExpr, String> {
    match expr {
        IntermediateExpr::Var(var) => Ok(VarOrConstMallocAccess::Var(var.clone()).into()),
        IntermediateExpr::Constant(scalar) => Ok(SimpleExpr::Constant(ConstExpression::scalar(*scalar))),
        IntermediateExpr::ArrayAccess { array, index } => {
            if let Some(&label) = const_malloc.map.get(array)
                && let IntermediateExpr::Constant(offset) = &**index
            {
                return Ok(VarOrConstMallocAccess::ConstMallocAccess {
                    malloc_label: label,
                    offset: ConstExpression::scalar(*offset),
                }
                .into());
            }

            let aux_arr = state.array_manager.get_aux_var(array, index);

            if !state.array_manager.valid.insert(aux_arr.clone()) {
                return Ok(VarOrConstMallocAccess::Var(aux_arr).into());
            }

            let simplified_index = simplify_expr(ctx, state, const_malloc, index, lines)?;
            handle_array_assignment(
                state,
                const_malloc,
                lines,
                array,
                &simplified_index,
                ArrayAccessType::VarIsAssigned(aux_arr.clone()),
            );
            Ok(VarOrConstMallocAccess::Var(aux_arr).into())
        }
        IntermediateExpr::Math { op, left, right } => {
            let arg0 = simplify_expr(ctx, state, const_malloc, left, lines)?;
            let arg1 = simplify_expr(ctx, state, const_malloc, right, lines)?;
            let aux_var = state.counters.aux_var();
            lines.push(SimpleLine::Assignment {
                var: aux_var.clone().into(),
                op: (*op).into(),
                arg0,
                arg1,
            });
            Ok(VarOrConstMallocAccess::Var(aux_var).into())
        }
        IntermediateExpr::FunctionCall {
            function,
            args,
            location,
        } => {
            let callee = ctx
                .functions
                .get(function)
                .ok_or_else(|| format!("Function used but not defined: {function}"))?;
            if callee.n_returned_vars != 1 {
                return Err(format!(
                    "Nested function calls must return exactly one value (function {function} returns {} values)",
                    callee.n_returned_vars
                ));
            }

            let simplified_args = args
                .iter()
                .map(|arg| simplify_expr(ctx, state, const_malloc, arg, lines))
                .collect::<Result<Vec<_>, _>>()?;

            let result_var = state.counters.aux_var();
            lines.push(SimpleLine::FunctionCall {
                function_name: function.clone(),
                args: simplified_args,
                return_data: vec![result_var.clone()],
                location: *location,
            });

            Ok(VarOrConstMallocAccess::Var(result_var).into())
        }
        IntermediateExpr::HintWitness { .. } => {
            Err("hint_witness(\"...\") is only valid as the right-hand side of an assignment".to_string())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ArrayAccessType {
    VarIsAssigned(Var),          // var = array[index]
    ArrayIsAssigned(SimpleExpr), // array[index] = expr
}

fn handle_array_assignment(
    state: &mut SimplifyState<'_>,
    const_malloc: &ConstMalloc,
    res: &mut Vec<SimpleLine>,
    array: &Var,
    simplified_index: &SimpleExpr,
    access_type: ArrayAccessType,
) {
    // const_malloc + constant index -> direct ADD (fp + offset), no DEREF.
    if let SimpleExpr::Constant(offset) = simplified_index
        && let Some(&label) = const_malloc.map.get(array)
    {
        let const_access = VarOrConstMallocAccess::ConstMallocAccess {
            malloc_label: label,
            offset: offset.clone(),
        };
        match access_type {
            ArrayAccessType::VarIsAssigned(var) => {
                res.push(SimpleLine::equality(var, const_access));
            }
            ArrayAccessType::ArrayIsAssigned(expr) => {
                res.push(SimpleLine::equality(const_access, expr));
            }
        }
        return;
    }

    let base_addr: SimpleExpr = VarOrConstMallocAccess::Var(array.clone()).into();

    let value_simplified = match access_type {
        ArrayAccessType::VarIsAssigned(var) => SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)),
        ArrayAccessType::ArrayIsAssigned(expr) => expr,
    };

    let (index_var, shift) = match simplified_index {
        SimpleExpr::Constant(c) => (base_addr, c.clone()),
        _ => {
            // ptr = base_addr + index
            let ptr_var = state.counters.aux_var();
            res.push(SimpleLine::Assignment {
                var: ptr_var.clone().into(),
                op: MathOperation::Add,
                arg0: base_addr,
                arg1: simplified_index.clone(),
            });
            (
                SimpleExpr::Memory(VarOrConstMallocAccess::Var(ptr_var)),
                ConstExpression::zero(),
            )
        }
    };

    res.push(SimpleLine::RawAccess {
        res: value_simplified,
        index: index_var,
        shift,
    });
}

fn create_recursive_function(
    name: String,
    location: SourceLocation,
    args: Vec<Var>,
    iterator: Var,
    end: SimpleExpr,
    mut body: Vec<SimpleLine>,
    external_vars: &[Var],
) -> SimpleFunction {
    let next_iter = format!("@incremented_{iterator}");
    body.push(SimpleLine::Assignment {
        var: next_iter.clone().into(),
        op: MathOperation::Add,
        arg0: iterator.clone().into(),
        arg1: SimpleExpr::one(),
    });

    let mut recursive_args: Vec<SimpleExpr> = vec![next_iter.into()];
    recursive_args.extend(external_vars.iter().map(|v| v.clone().into()));

    body.push(SimpleLine::FunctionCall {
        function_name: name.clone(),
        args: recursive_args,
        return_data: vec![],
        location,
    });
    body.push(SimpleLine::FunctionRet { return_data: vec![] });

    let diff_var = format!("@diff_{iterator}");

    let instructions = vec![
        SimpleLine::Assignment {
            var: diff_var.clone().into(),
            op: MathOperation::Sub,
            arg0: iterator.into(),
            arg1: end,
        },
        SimpleLine::IfNotZero {
            condition: diff_var.into(),
            then_branch: body,
            else_branch: vec![SimpleLine::FunctionRet { return_data: vec![] }],
            location,
        },
    ];

    SimpleFunction {
        name,
        arguments: args,
        n_returned_vars: 0,
        instructions,
    }
}

impl Display for SimpleLine {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.to_string_with_indent(0))
    }
}

impl SimpleLine {
    fn to_string_with_indent(&self, indent: usize) -> String {
        let spaces = "    ".repeat(indent);
        let line_str = match self {
            Self::ForwardDeclaration { var } => {
                format!("var {var}")
            }
            Self::Match { value, arms, offset } => {
                let arms_str = arms
                    .iter()
                    .enumerate()
                    .map(|(index, body)| {
                        let body = body
                            .iter()
                            .map(|line| line.to_string_with_indent(indent + 2))
                            .collect::<Vec<_>>()
                            .join("\n");

                        format!(
                            "{}{} => {{{}\n{}}}",
                            "    ".repeat(indent + 1),
                            index + offset,
                            body,
                            "    ".repeat(indent + 1),
                        )
                    })
                    .collect::<Vec<_>>()
                    .join("\n");

                format!("match {value} {{\n{arms_str}\n{spaces}}}")
            }

            Self::Assignment { var, op, arg0, arg1 } => {
                format!("{var} = {arg0} {op} {arg1}")
            }
            Self::CustomHint(hint, args) => {
                format!(
                    "{}({})",
                    hint.name(),
                    args.iter().map(|expr| format!("{expr}")).collect::<Vec<_>>().join(", ")
                )
            }
            Self::HintWitness { destination, name } => {
                format!("hint_witness(\"{name}\", {destination})")
            }
            Self::RawAccess { res, index, shift } => {
                format!("{res} = memory[{index} + {shift}]")
            }
            Self::IfNotZero {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                let then_str = then_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                let else_str = else_branch
                    .iter()
                    .map(|line| line.to_string_with_indent(indent + 1))
                    .collect::<Vec<_>>()
                    .join("\n");

                if else_branch.is_empty() {
                    format!("if {condition} != 0 {{\n{then_str}\n{spaces}}}")
                } else {
                    format!("if {condition} != 0 {{\n{then_str}\n{spaces}}} else {{\n{else_str}\n{spaces}}}")
                }
            }
            Self::FunctionCall {
                function_name,
                args,
                return_data,
                ..
            } => {
                let args_str = args.iter().map(|arg| format!("{arg}")).collect::<Vec<_>>().join(", ");
                let return_data_str = return_data
                    .iter()
                    .map(|var| var.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");

                if return_data.is_empty() {
                    format!("{function_name}({args_str})")
                } else {
                    format!("{return_data_str} = {function_name}({args_str})")
                }
            }
            Self::FunctionRet { return_data } => {
                let return_data_str = return_data
                    .iter()
                    .map(|arg| format!("{arg}"))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("return {return_data_str}")
            }
            Self::Precompile(precompile) => format!("{precompile}"),
            Self::Print { line_info: _, content } => {
                let content_str = content.iter().map(|c| format!("{c}")).collect::<Vec<_>>().join(", ");
                format!("print({content_str})")
            }
            Self::HintMAlloc { var, size } => {
                format!("{var} = Array({size})")
            }
            Self::ConstMalloc { var, size, label: _ } => {
                format!("{var} = Array({size})")
            }
            Self::Panic { message } => match message {
                Some(msg) => format!("assert False, \"{msg}\""),
                None => "assert False".to_string(),
            },
            Self::LocationReport { .. } => Default::default(),
            Self::DebugAssert { expr, .. } => {
                format!("debug_assert({expr})")
            }
            Self::AssertEq { left, right, .. } => {
                format!("assert_eq({left} == {right})")
            }
            Self::RangeCheck { val, bound } => {
                format!("range_check({val} <= {bound})")
            }
        };
        format!("{spaces}{line_str}")
    }
}

impl Display for SimpleFunction {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let args_str = self
            .arguments
            .iter()
            .map(|arg| arg.to_string())
            .collect::<Vec<_>>()
            .join(", ");

        let instructions_str = self
            .instructions
            .iter()
            .map(|line| line.to_string_with_indent(1))
            .collect::<Vec<_>>()
            .join("\n");

        if self.instructions.is_empty() {
            write!(f, "def {}({}) -> {} {{}}", self.name, args_str, self.n_returned_vars)
        } else {
            write!(
                f,
                "def {}({}) -> {} {{\n{}\n}}",
                self.name, args_str, self.n_returned_vars, instructions_str
            )
        }
    }
}

impl Display for SimpleProgram {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut first = true;
        for function in self.functions.values() {
            if !first {
                writeln!(f)?;
            }
            write!(f, "{function}")?;
            first = false;
        }
        Ok(())
    }
}
