/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{BinaryOperator, Location, NodeId};
use crate::hir;
use crate::mir::{self, BinaryOp, Block, FunctionBuilder, InstKind, Ty, UnaryOp, Value};
use crate::parse::PrefixOp;
use std::collections::HashMap;

pub(crate) fn translate(program: &hir::Program) -> mir::Program {
    let mut mir = mir::Program::default();
    for function in &program.funcs {
        mir.push_function(Lowerer::lower_function(function));
    }
    mir
}

struct Lowerer {
    builder: FunctionBuilder,
    binding_values: HashMap<NodeId, Value>,
}

enum Lowered {
    Continues { block: Block, value: Option<Value> },
    Terminated,
}

use Lowered::{Continues, Terminated};

impl Lowerer {
    fn lower_function(function: &hir::Function) -> mir::Function {
        let mut lowerer = Self {
            builder: FunctionBuilder::new(lower_type(&function.return_ty)),
            binding_values: HashMap::new(),
        };
        let entry = lowerer.builder.entry_block();
        if let Continues { block, value } = lowerer.lower_expr(entry, &function.body) {
            let value = lowerer.value_for_type(value, lowerer.builder.return_type().clone());
            lowerer
                .builder
                .return_(block, value, function.body.span.clone());
        }
        lowerer.builder.finish()
    }

    fn lower_expr(&mut self, block: Block, expr: &hir::Expr) -> Lowered {
        let ty = lower_type(&expr.ty);
        match &expr.kind {
            hir::ExprKind::Variable(binding) => Continues {
                block,
                value: Some(
                    *self
                        .binding_values
                        .get(binding)
                        .expect("HIR binding has no MIR value"),
                ),
            },
            hir::ExprKind::Bool(value) => Continues {
                block,
                value: Some(self.builder.append_inst(
                    block,
                    InstKind::BoolConst(*value),
                    ty,
                    expr.span.clone(),
                )),
            },
            hir::ExprKind::Int(value) => Continues {
                block,
                value: Some(self.builder.append_inst(
                    block,
                    InstKind::IntConst(*value),
                    ty,
                    expr.span.clone(),
                )),
            },
            hir::ExprKind::Float(value) => Continues {
                block,
                value: Some(self.builder.append_inst(
                    block,
                    InstKind::FloatConst(value.clone()),
                    ty,
                    expr.span.clone(),
                )),
            },
            hir::ExprKind::Block(statements) => self.lower_block(block, statements, ty),
            hir::ExprKind::IfElse(condition, then_branch, else_branch) => self.lower_if_else(
                block,
                condition,
                then_branch,
                else_branch.as_deref(),
                ty,
                &expr.span,
            ),
            hir::ExprKind::BinOp(left, op, right) => {
                if matches!(op, BinaryOperator::And | BinaryOperator::Or) {
                    self.lower_short_circuit(block, left, *op, right, &expr.span)
                } else {
                    self.lower_binary(block, left, *op, right, ty, &expr.span)
                }
            }
            hir::ExprKind::Unop(op, operand) => {
                self.lower_unary(block, op, operand, ty, &expr.span)
            }
            hir::ExprKind::String(_)
            | hir::ExprKind::Array(_)
            | hir::ExprKind::Tuple(_)
            | hir::ExprKind::FuncCall(_, _)
            | hir::ExprKind::IndexAccess(_, _) => unimplemented!(),
        }
    }

    fn lower_block(&mut self, block: Block, statements: &[hir::Stmt], ty: Ty) -> Lowered {
        let mut block = block;
        let mut value = None;
        for statement in statements {
            match self.lower_stmt(block, statement) {
                Continues {
                    block: next_block,
                    value: next_value,
                } => {
                    block = next_block;
                    value = next_value;
                }
                Terminated => return Terminated,
            };
        }
        Continues {
            block,
            value: self.value_for_type(value, ty),
        }
    }

    fn lower_stmt(&mut self, block: Block, stmt: &hir::Stmt) -> Lowered {
        match &stmt.kind {
            hir::StmtKind::Expr(expr) => self.lower_expr(block, expr),
            hir::StmtKind::Let(pattern, expr) => {
                let Continues { block, value } = self.lower_expr(block, expr) else {
                    return Terminated;
                };
                let value = value.expect("let expression must produce a value");
                match &pattern.kind {
                    hir::PatKind::Wildcard => {}
                    hir::PatKind::Binding(binding) => {
                        self.binding_values.insert(*binding, value);
                    }
                    _ => unimplemented!(),
                }
                Continues { block, value: None }
            }
            hir::StmtKind::Return(expr) => {
                let lowered = match expr {
                    Some(expr) => self.lower_expr(block, expr),
                    None => Continues { block, value: None },
                };
                let Continues { block, value } = lowered else {
                    return Terminated;
                };
                let value = self.value_for_type(value, self.builder.return_type().clone());
                self.builder.return_(block, value, stmt.span.clone());
                Terminated
            }
            hir::StmtKind::Var(_, _)
            | hir::StmtKind::Assign(_, _)
            | hir::StmtKind::Continue
            | hir::StmtKind::Break
            | hir::StmtKind::Loop => unimplemented!(),
        }
    }

    fn lower_if_else(
        &mut self,
        block: Block,
        condition: &hir::Expr,
        then_stmt: &hir::Stmt,
        else_stmt: Option<&hir::Stmt>,
        ty: Ty,
        span: &Location,
    ) -> Lowered {
        let Continues {
            block,
            value: condition,
        } = self.lower_expr(block, condition)
        else {
            return Terminated;
        };
        let condition = condition.expect("condition must produce a value");
        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        self.builder
            .branch(block, condition, then_block, else_block, span.clone());

        let then_path = self.lower_stmt(then_block, then_stmt);
        let else_path = match else_stmt {
            Some(stmt) => self.lower_stmt(else_block, stmt),
            None => Continues {
                block: else_block,
                value: None,
            },
        };

        self.merge([then_path, else_path], ty, span)
    }

    fn lower_short_circuit(
        &mut self,
        block: Block,
        left: &hir::Expr,
        op: BinaryOperator,
        right: &hir::Expr,
        span: &Location,
    ) -> Lowered {
        let Continues { block, value: left } = self.lower_expr(block, left) else {
            return Terminated;
        };
        let left = left.expect("operator must produce a value");
        let right_block = self.builder.create_block();
        let short_block = self.builder.create_block();
        let (then_block, else_block, short_value) = match op {
            BinaryOperator::And => (right_block, short_block, false),
            BinaryOperator::Or => (short_block, right_block, true),
            _ => unreachable!(),
        };
        self.builder
            .branch(block, left, then_block, else_block, span.clone());

        let right_path = self.lower_expr(right_block, right);

        let short_value = self.builder.append_inst(
            short_block,
            InstKind::BoolConst(short_value),
            Ty::Bool,
            span.clone(),
        );

        self.merge(
            [
                right_path,
                Continues {
                    block: short_block,
                    value: Some(short_value),
                },
            ],
            Ty::Bool,
            span,
        )
    }

    fn merge<const N: usize>(&mut self, paths: [Lowered; N], ty: Ty, span: &Location) -> Lowered {
        let paths: Vec<_> = paths
            .into_iter()
            .filter_map(|path| match path {
                Continues { block, value } => Some((block, value)),
                Terminated => None,
            })
            .collect();
        if paths.is_empty() {
            return Terminated;
        }

        let merge = self.builder.create_block();
        let result = (ty != Ty::Void).then(|| self.builder.append_block_param(merge, ty.clone()));
        for (block, value) in paths {
            let value = self.value_for_type(value, ty.clone());
            self.builder
                .jump(block, merge, value.into_iter().collect(), span.clone());
        }
        Continues {
            block: merge,
            value: result,
        }
    }

    fn lower_binary(
        &mut self,
        block: Block,
        left: &hir::Expr,
        op: BinaryOperator,
        right: &hir::Expr,
        ty: Ty,
        span: &Location,
    ) -> Lowered {
        let Continues { block, value: left } = self.lower_expr(block, left) else {
            return Terminated;
        };
        let left = left.expect("operator must produce a value");
        let Continues {
            block,
            value: right,
        } = self.lower_expr(block, right)
        else {
            return Terminated;
        };
        let right = right.expect("operator must produce a value");
        let op = lower_binary_op(op, self.builder.value_type(left));
        let value = self.builder.append_inst(
            block,
            InstKind::Binary { op, left, right },
            ty,
            span.clone(),
        );
        Continues {
            block,
            value: Some(value),
        }
    }

    fn lower_unary(
        &mut self,
        block: Block,
        op: &PrefixOp,
        operand: &hir::Expr,
        ty: Ty,
        span: &Location,
    ) -> Lowered {
        let Continues {
            block,
            value: operand,
        } = self.lower_expr(block, operand)
        else {
            return Terminated;
        };
        let operand = operand.expect("operator must produce a value");
        let op = match (op, self.builder.value_type(operand)) {
            (PrefixOp::Not, Ty::Bool) => UnaryOp::BoolNot,
            (PrefixOp::Minus, Ty::Int) => UnaryOp::IntNeg,
            (PrefixOp::Minus, Ty::Float) => UnaryOp::FloatNeg,
            _ => unreachable!("operator must be valid for its operand type"),
        };
        let value =
            self.builder
                .append_inst(block, InstKind::Unary { op, operand }, ty, span.clone());
        Continues {
            block,
            value: Some(value),
        }
    }

    fn value_for_type(&self, value: Option<Value>, ty: Ty) -> Option<Value> {
        if ty == Ty::Void {
            None
        } else {
            Some(value.unwrap_or_else(|| panic!("expected a value of type {ty}")))
        }
    }
}

fn lower_type(ty: &hir::Type) -> Ty {
    match ty {
        hir::Type::Void => Ty::Void,
        hir::Type::Never => Ty::Never,
        hir::Type::Bool => Ty::Bool,
        hir::Type::Int => Ty::Int,
        hir::Type::Float => Ty::Float,
        _ => unimplemented!(),
    }
}

fn lower_binary_op(op: BinaryOperator, ty: &Ty) -> BinaryOp {
    use BinaryOp::*;
    use BinaryOperator::*;

    match (op, ty) {
        (Add, Ty::Int) => IntAdd,
        (Subtract, Ty::Int) => IntSubtract,
        (Multiply, Ty::Int) => IntMultiply,
        (Divide, Ty::Int) => IntDivide,
        (Mod, Ty::Int) => IntModulo,
        (Pow, Ty::Int) => IntPow,
        (Add, Ty::Float) => FloatAdd,
        (Subtract, Ty::Float) => FloatSubtract,
        (Multiply, Ty::Float) => FloatMultiply,
        (Divide, Ty::Float) => FloatDivide,
        (Pow, Ty::Float) => FloatPow,
        (Equal, Ty::Int) => IntEqual,
        (NotEqual, Ty::Int) => IntNotEqual,
        (LessThan, Ty::Int) => IntLessThan,
        (LessThanOrEqual, Ty::Int) => IntLessThanOrEqual,
        (GreaterThan, Ty::Int) => IntGreaterThan,
        (GreaterThanOrEqual, Ty::Int) => IntGreaterThanOrEqual,
        (Equal, Ty::Float) => FloatEqual,
        (NotEqual, Ty::Float) => FloatNotEqual,
        (LessThan, Ty::Float) => FloatLessThan,
        (LessThanOrEqual, Ty::Float) => FloatLessThanOrEqual,
        (GreaterThan, Ty::Float) => FloatGreaterThan,
        (GreaterThanOrEqual, Ty::Float) => FloatGreaterThanOrEqual,
        (Equal, Ty::Bool) => BoolEqual,
        (NotEqual, Ty::Bool) => BoolNotEqual,
        _ => unimplemented!(),
    }
}
