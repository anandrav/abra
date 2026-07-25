/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{Expr, ExprKind, FileAst, ItemKind, Pat, PatKind, Stmt, StmtKind};
use crate::hir;
use crate::statics::{Declaration, StaticsContext, Type};
use std::rc::Rc;

pub(crate) fn translate(ctx: &StaticsContext, file_asts: &[Rc<FileAst>]) -> hir::Program {
    let translator = Translator { ctx };
    let mut funcs = vec![];

    if let Some(main_ast) = file_asts.first() {
        let statements = main_ast
            .items
            .iter()
            .filter_map(|item| match &*item.kind {
                ItemKind::Stmt(statement) => Some(translator.stmt(statement)),
                _ => None,
            })
            .collect();
        funcs.push(hir::Function {
            return_ty: Type::Void,
            body: hir::Expr {
                ty: Type::Void,
                kind: hir::ExprKind::Block(statements),
                span: main_ast.loc.clone(),
            },
        });
    }

    hir::Program { funcs }
}

struct Translator<'a> {
    ctx: &'a StaticsContext,
}

impl Translator<'_> {
    fn stmt(&self, statement: &Rc<Stmt>) -> hir::Stmt {
        let kind = match &*statement.kind {
            StmtKind::Let(mutable, (pattern, _), expr) => {
                let pattern = self.pat(pattern);
                let expr = self.expr(expr).into();
                if *mutable {
                    hir::StmtKind::Var(pattern, expr)
                } else {
                    hir::StmtKind::Let(pattern, expr)
                }
            }
            StmtKind::Assign(_, _, _) => unimplemented!(),
            StmtKind::Expr(expr) => hir::StmtKind::Expr(self.expr(expr).into()),
            StmtKind::Continue => hir::StmtKind::Continue,
            StmtKind::Break => hir::StmtKind::Break,
            StmtKind::Return(expr) => {
                hir::StmtKind::Return(expr.as_ref().map(|expr| self.expr(expr).into()))
            }
            StmtKind::WhileLoop(_, _) => unimplemented!(),
            StmtKind::ForLoop(_, _, _) => unimplemented!(),
        };

        hir::Stmt {
            kind,
            span: statement.loc.clone(),
        }
    }

    fn expr(&self, expr: &Rc<Expr>) -> hir::Expr {
        let kind = match &*expr.kind {
            ExprKind::Variable(_) => {
                let Declaration::Var(declaration) = &self.ctx.resolution_map[&expr.id] else {
                    unimplemented!()
                };
                hir::ExprKind::Variable(declaration.id())
            }
            ExprKind::Nil => unimplemented!(),
            ExprKind::Int(value) => hir::ExprKind::Int(*value),
            ExprKind::Float(value) => hir::ExprKind::Float(value.clone()),
            ExprKind::Bool(value) => hir::ExprKind::Bool(*value),
            ExprKind::Str(value) => hir::ExprKind::String(value.clone()),
            ExprKind::Array(elements) => hir::ExprKind::Array(
                elements
                    .iter()
                    .map(|element| self.expr(element).into())
                    .collect(),
            ),
            ExprKind::AnonymousFunction(_, _, _) => unimplemented!(),
            ExprKind::IfElse(condition, then_branch, else_branch) => hir::ExprKind::IfElse(
                self.expr(condition).into(),
                self.stmt(then_branch).into(),
                else_branch.as_ref().map(|branch| self.stmt(branch).into()),
            ),
            ExprKind::Match(_, _) => unimplemented!(),
            ExprKind::Block(statements) => hir::ExprKind::Block(
                statements
                    .iter()
                    .map(|statement| self.stmt(statement))
                    .collect(),
            ),
            ExprKind::BinOp(left, op, right) => {
                hir::ExprKind::BinOp(self.expr(left).into(), *op, self.expr(right).into())
            }
            ExprKind::Unop(op, operand) => {
                hir::ExprKind::Unop(op.clone(), self.expr(operand).into())
            }
            ExprKind::FuncCall(_, _) => unimplemented!(),
            ExprKind::Tuple(elements) => hir::ExprKind::Tuple(
                elements
                    .iter()
                    .map(|element| self.expr(element).into())
                    .collect(),
            ),
            ExprKind::MemberAccess(_, _) => unimplemented!(),
            ExprKind::MemberAccessLeadingDot(_) => unimplemented!(),
            ExprKind::IndexAccess(array, index) => {
                hir::ExprKind::IndexAccess(self.expr(array).into(), self.expr(index).into())
            }
            ExprKind::Unwrap(_) => unimplemented!(),
            ExprKind::Try(_) => unimplemented!(),
            ExprKind::TaskBlock(_) => unimplemented!(),
        };

        hir::Expr {
            ty: self.ctx.solution_of_node(expr.node()).unwrap(),
            kind,
            span: expr.loc.clone(),
        }
    }

    fn pat(&self, pattern: &Rc<Pat>) -> hir::Pat {
        let kind = match &*pattern.kind {
            PatKind::Wildcard => hir::PatKind::Wildcard,
            PatKind::Binding(_) => hir::PatKind::Binding(pattern.id),
            PatKind::Variant(_, _, _) => unimplemented!(),
            PatKind::Void => hir::PatKind::Void,
            PatKind::Int(value) => hir::PatKind::Int(*value),
            PatKind::Float(value) => hir::PatKind::Float(value.clone()),
            PatKind::Bool(value) => hir::PatKind::Bool(*value),
            PatKind::Str(value) => hir::PatKind::Str(value.clone()),
            PatKind::Tuple(elements) => hir::PatKind::Tuple(
                elements
                    .iter()
                    .map(|element| self.pat(element).into())
                    .collect(),
            ),
            PatKind::Struct(_, _) => unimplemented!(),
            PatKind::Or(_, _) => unimplemented!(),
        };

        hir::Pat {
            ty: self.ctx.solution_of_node(pattern.node()).unwrap(),
            kind,
            span: pattern.loc.clone(),
        }
    }
}
