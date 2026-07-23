use crate::ast::{Expr, ExprKind, FileAst, ItemKind, Pat, PatKind, Stmt, StmtKind};
use crate::hir;
use std::rc::Rc;

pub(crate) fn translate(file_asts: &[Rc<FileAst>]) -> hir::Program {
    let mut funcs = vec![];

    // main function
    if let Some(main_ast) = file_asts.first() {
        let mut stmts = vec![];
        for item in main_ast.items.iter() {
            match &*item.kind {
                ItemKind::FuncDecl(_)
                | ItemKind::FuncDef(_)
                | ItemKind::TypeDef(_)
                | ItemKind::InterfaceDef(_)
                | ItemKind::InterfaceImpl(_)
                | ItemKind::Extension(_)
                | ItemKind::Import(_, _) => {}
                ItemKind::Stmt(stmt) => stmts.push(stmt.translate()),
            }
        }
        let body = hir::Expr {
            kind: hir::ExprKind::Block(stmts),
            span: main_ast.loc.clone(),
        };
        funcs.push(hir::Function { body })
    }

    hir::Program { funcs }
}

impl Stmt {
    fn translate(&self) -> hir::Stmt {
        let kind = match &*self.kind {
            StmtKind::Let(_, _, _) => unimplemented!(),
            StmtKind::Assign(_, _, _) => unimplemented!(),
            StmtKind::Expr(expr) => hir::StmtKind::Expr(expr.translate().into()),
            StmtKind::Continue => hir::StmtKind::Continue,
            StmtKind::Break => hir::StmtKind::Break,
            StmtKind::Return(expr) => {
                hir::StmtKind::Return(expr.as_ref().map(|e| e.translate().into()))
            }
            StmtKind::WhileLoop(_, _) => unimplemented!(),
            StmtKind::ForLoop(_, _, _) => unimplemented!(),
        };

        hir::Stmt {
            kind,
            span: self.loc.clone(),
        }
    }
}

impl Expr {
    fn translate(&self) -> hir::Expr {
        let kind = match &*self.kind {
            ExprKind::Variable(_) => unimplemented!(),
            ExprKind::Nil => unimplemented!(),
            ExprKind::Int(n) => hir::ExprKind::Int(*n),
            ExprKind::Float(f) => hir::ExprKind::Float(f.clone()),
            ExprKind::Bool(b) => hir::ExprKind::Bool(*b),
            ExprKind::Str(s) => hir::ExprKind::String(s.clone()),
            ExprKind::Array(arr) => {
                hir::ExprKind::Array(arr.iter().map(|e| e.translate().into()).collect())
            }
            ExprKind::AnonymousFunction(_, _, _) => unimplemented!(),
            ExprKind::IfElse(cond, tbranch, ebranch) => hir::ExprKind::IfElse(
                cond.translate().into(),
                tbranch.translate().into(),
                ebranch.clone().map(|s| s.translate().into()),
            ),
            ExprKind::Match(_, _) => unimplemented!(),
            ExprKind::Block(stmts) => {
                hir::ExprKind::Block(stmts.iter().map(|e| e.translate()).collect())
            }
            ExprKind::BinOp(_, _, _) => unimplemented!(),
            ExprKind::Unop(_, _) => unimplemented!(),
            ExprKind::FuncCall(_, _) => unimplemented!(),
            ExprKind::Tuple(elems) => {
                hir::ExprKind::Tuple(elems.iter().map(|e| e.translate().into()).collect())
            }
            ExprKind::MemberAccess(_, _) => unimplemented!(),
            ExprKind::MemberAccessLeadingDot(_) => unimplemented!(),
            ExprKind::IndexAccess(_, _) => unimplemented!(),
            ExprKind::Unwrap(_) => unimplemented!(),
            ExprKind::Try(_) => unimplemented!(),
            ExprKind::TaskBlock(_) => unimplemented!(),
        };

        hir::Expr {
            kind,
            span: self.loc.clone(),
        }
    }
}

impl Pat {
    fn translate(&self) -> hir::Pat {
        let kind = match &*self.kind {
            PatKind::Wildcard => hir::PatKind::Wildcard,
            PatKind::Binding(s) => hir::PatKind::Binding(s.clone()),
            PatKind::Variant(_, _, _) => unimplemented!(),
            PatKind::Void => hir::PatKind::Void,
            PatKind::Int(n) => hir::PatKind::Int(*n),
            PatKind::Float(f) => hir::PatKind::Float(f.clone()),
            PatKind::Bool(b) => hir::PatKind::Bool(*b),
            PatKind::Str(s) => hir::PatKind::Str(s.clone()),
            PatKind::Tuple(elems) => {
                hir::PatKind::Tuple(elems.iter().map(|p| p.translate().into()).collect())
            }
            PatKind::Struct(_, _) => unimplemented!(),
            PatKind::Or(_, _) => unimplemented!(),
        };

        hir::Pat {
            kind,
            span: self.loc.clone(),
        }
    }
}
