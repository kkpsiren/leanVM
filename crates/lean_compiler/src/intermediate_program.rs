//! The intermediate zkDSL, as its own AST: the contract between the two
//! compilation stages. The constructs the first stage eliminates (mutables,
//! `unroll`, `@inline`, `Const` args, compile-time constants, multidimensional
//! indexing) are unrepresentable here. The only constructor is
//! [`IntermediateProgram::from_parsed`], which converts (and validates) a
//! parsed [`Program`].

use crate::{F, ast_passes::check_program_scoping, lang::*};
use lean_vm::BooleanExpr;
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone)]
pub struct IntermediateProgram {
    pub functions: BTreeMap<FunctionName, IntermediateFunction>,
    pub function_locations: BTreeMap<SourceLocation, FunctionName>,
    pub source_code: BTreeMap<FileId, String>,
    pub filepaths: BTreeMap<FileId, String>,
}

#[derive(Debug, Clone)]
pub struct IntermediateFunction {
    pub name: FunctionName,
    pub arguments: Vec<Var>,
    pub n_returned_vars: usize,
    pub body: Vec<IntermediateLine>,
}

#[derive(Debug, Clone)]
pub enum IntermediateLine {
    Declaration {
        var: Var,
    },
    Statement {
        targets: Vec<IntermediateTarget>, // can be empty for standalone calls
        value: IntermediateExpr,
        location: SourceLocation,
    },
    Assert {
        debug: bool,
        boolean: BooleanExpr<IntermediateExpr>,
        location: SourceLocation,
    },
    IfCondition {
        condition: BooleanExpr<IntermediateExpr>,
        then_branch: Vec<Self>,
        else_branch: Vec<Self>,
        location: SourceLocation,
    },
    Match {
        value: IntermediateExpr,
        arms: Vec<(usize, Vec<Self>)>,
        location: SourceLocation,
    },
    ForLoop {
        iterator: Var,
        start: IntermediateExpr,
        end: IntermediateExpr,
        body: Vec<Self>,
        parallel: bool,
        location: SourceLocation,
    },
    FunctionRet {
        return_data: Vec<IntermediateExpr>,
    },
    Panic {
        message: Option<String>,
    },
    /// noop, debug purpose only
    LocationReport {
        location: SourceLocation,
    },
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediateTarget {
    Var(Var),
    ArrayAccess { array: Var, index: IntermediateExpr },
}

/// The runtime field operations (compile-time-only ops are folded away during
/// conversion, so a constant is always a plain field element).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediateOp {
    Add,
    Sub,
    Mul,
    Div,
}

impl IntermediateOp {
    fn from_math(op: MathOperation) -> Option<Self> {
        match op {
            MathOperation::Add => Some(Self::Add),
            MathOperation::Sub => Some(Self::Sub),
            MathOperation::Mul => Some(Self::Mul),
            MathOperation::Div => Some(Self::Div),
            _ => None,
        }
    }
}

impl From<IntermediateOp> for MathOperation {
    fn from(op: IntermediateOp) -> Self {
        match op {
            IntermediateOp::Add => Self::Add,
            IntermediateOp::Sub => Self::Sub,
            IntermediateOp::Mul => Self::Mul,
            IntermediateOp::Div => Self::Div,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum IntermediateExpr {
    Var(Var),
    Constant(F),
    ArrayAccess {
        array: Var,
        index: Box<Self>,
    },
    Math {
        op: IntermediateOp,
        left: Box<Self>,
        right: Box<Self>,
    },
    FunctionCall {
        function: FunctionName,
        args: Vec<Self>,
        location: SourceLocation,
    },
    /// `hint_witness("name", ptr)` — writes the next witness entry for `name`
    /// into the buffer pointed to by `ptr`.
    HintWitness {
        name: String,
        ptr: Box<Self>,
    },
}

impl IntermediateExpr {
    pub fn inner_exprs(&self) -> Vec<&Self> {
        match self {
            Self::Var(_) | Self::Constant(_) => vec![],
            Self::ArrayAccess { index, .. } => vec![index],
            Self::Math { left, right, .. } => vec![left, right],
            Self::FunctionCall { args, .. } => args.iter().collect(),
            Self::HintWitness { ptr, .. } => vec![ptr],
        }
    }
}

// Conversion from the parsed AST (= validation of the intermediate subset).

impl IntermediateProgram {
    /// Converts a parsed [`Program`] into the intermediate AST, rejecting every
    /// construct outside the subset. Holding an `IntermediateProgram` is proof
    /// that the program is in the subset (and well-scoped).
    pub fn from_parsed(program: Program) -> Result<Self, String> {
        check_program_scoping(&program)?;
        if let Some(name) = program.const_arrays.keys().next() {
            return Err(format!(
                "const array `{name}`: compile-time constant arrays are not part of the intermediate zkDSL"
            ));
        }
        let mut functions = BTreeMap::new();
        for (name, func) in program.functions {
            let func = convert_function(func).map_err(|e| format!("function `{name}`: {e}"))?;
            functions.insert(name, func);
        }
        Ok(Self {
            functions,
            function_locations: program.function_locations,
            source_code: program.source_code,
            filepaths: program.filepaths,
        })
    }
}

fn convert_function(func: Function) -> Result<IntermediateFunction, String> {
    if func.inlined {
        return Err("`@inline` functions are not part of the intermediate zkDSL".to_string());
    }
    if func.has_const_arguments() {
        return Err("`Const` arguments are not part of the intermediate zkDSL".to_string());
    }
    Ok(IntermediateFunction {
        name: func.name,
        arguments: func.arguments.into_iter().map(|arg| arg.name).collect(),
        n_returned_vars: func.n_returned_vars,
        body: convert_lines(func.body)?,
    })
}

fn convert_lines(lines: Vec<Line>) -> Result<Vec<IntermediateLine>, String> {
    lines.into_iter().map(convert_line).collect()
}

fn convert_line(line: Line) -> Result<IntermediateLine, String> {
    Ok(match line {
        Line::ForwardDeclaration { var, is_mutable } => {
            if is_mutable {
                return Err(format!(
                    "mutable variable `{var}` - mutable variables are not part of the intermediate zkDSL"
                ));
            }
            IntermediateLine::Declaration { var }
        }
        Line::Statement {
            targets,
            value,
            location,
        } => IntermediateLine::Statement {
            targets: targets.into_iter().map(convert_target).collect::<Result<_, _>>()?,
            value: convert_expr(value)?,
            location,
        },
        Line::Assert {
            debug,
            boolean,
            location,
        } => IntermediateLine::Assert {
            debug,
            boolean: convert_boolean(boolean)?,
            location,
        },
        Line::IfCondition {
            condition,
            then_branch,
            else_branch,
            location,
        } => IntermediateLine::IfCondition {
            condition: convert_boolean(condition)?,
            then_branch: convert_lines(then_branch)?,
            else_branch: convert_lines(else_branch)?,
            location,
        },
        Line::Match { value, arms, location } => IntermediateLine::Match {
            value: convert_expr(value)?,
            arms: arms
                .into_iter()
                .map(|(pattern, body)| Ok((pattern, convert_lines(body)?)))
                .collect::<Result<_, String>>()?,
            location,
        },
        Line::ForLoop {
            iterator,
            start,
            end,
            body,
            loop_kind,
            location,
        } => {
            if loop_kind.is_unroll() {
                return Err(format!(
                    "`unroll` loop at {location} - unrolled loops are not part of the intermediate zkDSL"
                ));
            }
            IntermediateLine::ForLoop {
                iterator,
                start: convert_expr(start)?,
                end: convert_expr(end)?,
                body: convert_lines(body)?,
                parallel: loop_kind.is_parallel(),
                location,
            }
        }
        Line::FunctionRet { return_data } => IntermediateLine::FunctionRet {
            return_data: return_data.into_iter().map(convert_expr).collect::<Result<_, _>>()?,
        },
        Line::Panic { message } => IntermediateLine::Panic { message },
        Line::LocationReport { location } => IntermediateLine::LocationReport { location },
    })
}

fn convert_target(target: AssignmentTarget) -> Result<IntermediateTarget, String> {
    Ok(match target {
        AssignmentTarget::Var { var, is_mutable } => {
            if is_mutable {
                return Err(format!(
                    "mutable variable `{var}` - mutable variables are not part of the intermediate zkDSL"
                ));
            }
            IntermediateTarget::Var(var)
        }
        AssignmentTarget::ArrayAccess { array, index } => IntermediateTarget::ArrayAccess {
            array: simple_expr_as_var(array)?,
            index: convert_expr(*index)?,
        },
    })
}

fn convert_boolean(boolean: BooleanExpr<Expression>) -> Result<BooleanExpr<IntermediateExpr>, String> {
    Ok(BooleanExpr {
        left: convert_expr(boolean.left)?,
        right: convert_expr(boolean.right)?,
        kind: boolean.kind,
    })
}

fn convert_expr(expr: Expression) -> Result<IntermediateExpr, String> {
    Ok(match expr {
        Expression::Value(value) => match value {
            SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => IntermediateExpr::Var(var),
            SimpleExpr::Memory(VarOrConstMallocAccess::ConstMallocAccess { .. }) => {
                return Err("internal memory accesses cannot appear in a source-level program".to_string());
            }
            SimpleExpr::Constant(constant) => IntermediateExpr::Constant(
                constant
                    .naive_eval()
                    .ok_or_else(|| format!("symbolic constant `{constant}` cannot appear in a source-level program"))?,
            ),
        },
        Expression::ArrayAccess { array, index } => {
            let array = simple_expr_as_var(array)?;
            if index.len() != 1 {
                return Err(format!(
                    "`{array}[..][..]`: multidimensional indexing is only supported on compile-time const \
                     arrays, which are not part of the intermediate zkDSL"
                ));
            }
            IntermediateExpr::ArrayAccess {
                array,
                index: Box::new(convert_expr(index.into_iter().next().unwrap())?),
            }
        }
        Expression::MathExpr(op, args) => {
            let args: Vec<IntermediateExpr> = args.into_iter().map(convert_expr).collect::<Result<_, _>>()?;
            // Constant expressions are evaluated eagerly.
            let constants: Option<Vec<F>> = args
                .iter()
                .map(|arg| match arg {
                    IntermediateExpr::Constant(scalar) => Some(*scalar),
                    _ => None,
                })
                .collect();
            if let Some(constants) = constants {
                let value = op
                    .eval(&constants)
                    .ok_or_else(|| format!("compile-time evaluation of `{op}` failed"))?;
                IntermediateExpr::Constant(value)
            } else {
                let runtime_op = IntermediateOp::from_math(op)
                    .ok_or_else(|| format!("Operation `{op}` is compile-time only; all operands must be constants"))?;
                let [left, right]: [IntermediateExpr; 2] = args
                    .try_into()
                    .map_err(|_| "runtime math operations take exactly two operands".to_string())?;
                IntermediateExpr::Math {
                    op: runtime_op,
                    left: Box::new(left),
                    right: Box::new(right),
                }
            }
        }
        Expression::FunctionCall {
            function_name,
            args,
            location,
        } => {
            if function_name == "match_range" {
                return Err("`match_range` is not part of the intermediate zkDSL (use `match`)".to_string());
            }
            IntermediateExpr::FunctionCall {
                function: function_name,
                args: args.into_iter().map(convert_expr).collect::<Result<_, _>>()?,
                location,
            }
        }
        Expression::Len { array, .. } => {
            return Err(format!(
                "`len({array})` is not part of the intermediate zkDSL (it only applies to compile-time const arrays)"
            ));
        }
        Expression::Lambda { .. } => {
            return Err("lambda expressions are not part of the intermediate zkDSL".to_string());
        }
        Expression::HintWitness { name, ptr } => IntermediateExpr::HintWitness {
            name,
            ptr: Box::new(convert_expr(*ptr)?),
        },
    })
}

fn simple_expr_as_var(expr: SimpleExpr) -> Result<Var, String> {
    match expr {
        SimpleExpr::Memory(VarOrConstMallocAccess::Var(var)) => Ok(var),
        other => Err(format!("array base must be a plain variable, got `{other}`")),
    }
}

/// Returns (internal_vars, external_vars). Used by the loop -> recursion lowering.
pub fn find_variable_usage(lines: &[IntermediateLine]) -> (BTreeSet<Var>, BTreeSet<Var>) {
    let mut internal_vars = BTreeSet::new();
    let mut external_vars = BTreeSet::new();

    let on_new_expr = |expr: &IntermediateExpr, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
        for var in vars_in_expression(expr) {
            if !internal_vars.contains(&var) {
                external_vars.insert(var);
            }
        }
    };

    let on_new_boolean =
        |boolean: &BooleanExpr<IntermediateExpr>, internal_vars: &BTreeSet<Var>, external_vars: &mut BTreeSet<Var>| {
            on_new_expr(&boolean.left, internal_vars, external_vars);
            on_new_expr(&boolean.right, internal_vars, external_vars);
        };

    for line in lines {
        match line {
            IntermediateLine::Declaration { var } => {
                internal_vars.insert(var.clone());
            }
            IntermediateLine::Match { value, arms, .. } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                // Arms are analyzed independently: a var read from the enclosing
                // scope in one arm stays external even if a sibling arm assigns a
                // same-named local.
                let arm_usages: Vec<_> = arms
                    .iter()
                    .map(|(_, statements)| find_variable_usage(statements))
                    .collect();
                for (_, arm_external) in &arm_usages {
                    external_vars.extend(arm_external.iter().filter(|v| !internal_vars.contains(*v)).cloned());
                }
                for (arm_internal, _) in arm_usages {
                    internal_vars.extend(arm_internal.into_iter().filter(|v| !external_vars.contains(v)));
                }
            }
            IntermediateLine::Statement { targets, value, .. } => {
                on_new_expr(value, &internal_vars, &mut external_vars);
                for target in targets {
                    match target {
                        IntermediateTarget::Var(var) => {
                            if !external_vars.contains(var) {
                                internal_vars.insert(var.clone());
                            }
                        }
                        IntermediateTarget::ArrayAccess { array, index } => {
                            if !internal_vars.contains(array) {
                                external_vars.insert(array.clone());
                            }
                            on_new_expr(index, &internal_vars, &mut external_vars);
                        }
                    }
                }
            }
            IntermediateLine::IfCondition {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                on_new_boolean(condition, &internal_vars, &mut external_vars);

                let (then_internal, then_external) = find_variable_usage(then_branch);
                let (else_internal, else_external) = find_variable_usage(else_branch);

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
            IntermediateLine::Assert { boolean, .. } => {
                on_new_boolean(boolean, &internal_vars, &mut external_vars);
            }
            IntermediateLine::FunctionRet { return_data } => {
                for ret in return_data {
                    on_new_expr(ret, &internal_vars, &mut external_vars);
                }
            }
            IntermediateLine::ForLoop {
                iterator,
                start,
                end,
                body,
                ..
            } => {
                let (body_internal, body_external) = find_variable_usage(body);
                internal_vars.extend(body_internal);
                internal_vars.insert(iterator.clone());
                external_vars.extend(body_external.difference(&internal_vars).cloned());
                on_new_expr(start, &internal_vars, &mut external_vars);
                on_new_expr(end, &internal_vars, &mut external_vars);
            }
            IntermediateLine::Panic { .. } | IntermediateLine::LocationReport { .. } => {}
        }
    }

    (internal_vars, external_vars)
}

pub fn vars_in_expression(expr: &IntermediateExpr) -> BTreeSet<Var> {
    let mut vars = BTreeSet::new();
    match expr {
        IntermediateExpr::Var(var) => {
            vars.insert(var.clone());
        }
        IntermediateExpr::ArrayAccess { array, .. } => {
            vars.insert(array.clone());
        }
        _ => {}
    }
    for inner_expr in expr.inner_exprs() {
        vars.extend(vars_in_expression(inner_expr));
    }
    vars
}
