use std::rc::Rc;
use crate::ast::{Expr, ExprKind, FileAst, ItemKind, Stmt, StmtKind, Pat, PatKind};
use crate::hir;

pub(crate) fn translate(file_asts: &[Rc<FileAst>]) -> hir::Program {
    let mut funcs = vec![];

    // main function
    if let Some(main_ast) = file_asts.first() {
        let mut stmts = vec![];
        for item in main_ast.items.iter() {
            match &*item.kind {
                ItemKind::FuncDecl(_)|
                ItemKind::FuncDef(_) |
                ItemKind::TypeDef(_)|
                ItemKind::InterfaceDef(_) |
                ItemKind::InterfaceImpl(_) |
                ItemKind::Extension(_) |
                ItemKind::Import(_, _) => {}
                ItemKind::Stmt(stmt) => {
                    stmts.push(stmt.translate())
                }
            }
        }
        let body = hir::Expr::Block(stmts);
        funcs.push(hir::Function { body })
    }

    hir::Program {
        funcs
    }
}

impl Stmt {
    fn translate(&self) -> hir::Stmt {
        match &*self.kind {
            StmtKind::Let(_, _, _) => unimplemented!(),
            StmtKind::Assign(_, _, _) => unimplemented!(),
            StmtKind::Expr(expr) => hir::Stmt::Expr(expr.translate().into()),
            StmtKind::Continue => hir::Stmt::Continue,
            StmtKind::Break => hir::Stmt::Break,
            StmtKind::Return(expr) => hir::Stmt::Return(expr.as_ref().map(|e| e.translate().into())),
            StmtKind::WhileLoop(_, _) => unimplemented!(),
            StmtKind::ForLoop(_, _, _) => unimplemented!(),
        }
    }
}

impl Expr {
    fn translate(&self) -> hir::Expr {
        match &*self.kind {
            ExprKind::Variable(_) => unimplemented!(),
            ExprKind::Nil => unimplemented!(),
            ExprKind::Int(n) => hir::Expr::Int(*n),
            ExprKind::Float(f) => hir::Expr::Float(f.clone()),
            ExprKind::Bool(b) => hir::Expr::Bool(*b),
            ExprKind::Str(s) => hir::Expr::String(s.clone()),
            ExprKind::Array(arr) => hir::Expr::Array(arr.iter().map(|e| e.translate().into()).collect()),
            ExprKind::AnonymousFunction(_, _, _) => unimplemented!(),
            ExprKind::IfElse(cond, tbranch, ebranch) => hir::Expr::IfElse(cond.translate().into(), tbranch.translate().into(), ebranch.clone().map(|s| s.translate().into())),
            ExprKind::Match(_, _) => unimplemented!(),
            ExprKind::Block(stmts) => hir::Expr::Block(stmts.iter().map(|e| e.translate()).collect()),
            ExprKind::BinOp(_, _, _) => unimplemented!(),
            ExprKind::Unop(_, _) => unimplemented!(),
            ExprKind::FuncCall(_, _) => unimplemented!(),
            ExprKind::Tuple(elems) => hir::Expr::Tuple(elems.iter().map(|e| e.translate().into()).collect()),
            ExprKind::MemberAccess(_, _) => unimplemented!(),
            ExprKind::MemberAccessLeadingDot(_) => unimplemented!(),
            ExprKind::IndexAccess(_, _) => unimplemented!(),
            ExprKind::Unwrap(_) => unimplemented!(),
            ExprKind::Try(_) => unimplemented!(),
            ExprKind::TaskBlock(_) => unimplemented!(),
        }
    }
}

impl Pat {
    fn translate(&self) -> hir::Pat {
        match &*self.kind {
            PatKind::Wildcard => hir::Pat::Wildcard,
            PatKind::Binding(s) => hir::Pat::Binding(s.clone()),
            PatKind::Variant(_, _, _) => unimplemented!(),
            PatKind::Void => hir::Pat::Void,
            PatKind::Int(n) => hir::Pat::Int(*n),
            PatKind::Float(f) => hir::Pat::Float(f.clone()),
            PatKind::Bool(b) => hir::Pat::Bool(*b),
            PatKind::Str(s) => hir::Pat::Str(s.clone()),
            PatKind::Tuple(elems) => hir::Pat::Tuple(elems.iter().map(|p| p.translate().into()).collect()),
            PatKind::Struct(_, _) => unimplemented!(),
            PatKind::Or(_, _) => unimplemented!(),
        }
    }
}