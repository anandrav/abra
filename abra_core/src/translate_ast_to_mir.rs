use crate::ast::{Expr, ExprKind, FileAst, ItemKind, NodeId, Pat, PatKind, Stmt, StmtKind};
use crate::mir;
use crate::statics::StaticsContext;
use std::rc::Rc;

pub(crate) fn translate(ctx: &StaticsContext, file_asts: &[Rc<FileAst>]) -> mir::Program {
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
        let body = mir::Expr {
            kind: mir::ExprKind::Block(stmts),
            span: main_ast.loc.clone(),
            id: NodeId::new(),
        };
        funcs.push(mir::Function { body })
    }

    mir::Program { funcs }
}

impl Stmt {
    fn translate(&self) -> mir::Stmt {
        let kind = match &*self.kind {
            StmtKind::Let(_, _, _) => unimplemented!(),
            StmtKind::Assign(_, _, _) => unimplemented!(),
            StmtKind::Expr(expr) => mir::StmtKind::Expr(expr.translate().into()),
            StmtKind::Continue => mir::StmtKind::Continue,
            StmtKind::Break => mir::StmtKind::Break,
            StmtKind::Return(expr) => {
                mir::StmtKind::Return(expr.as_ref().map(|e| e.translate().into()))
            }
            StmtKind::WhileLoop(_, _) => unimplemented!(),
            StmtKind::ForLoop(_, _, _) => unimplemented!(),
        };

        mir::Stmt {
            kind,
            span: self.loc.clone(),
        }
    }
}

impl Expr {
    fn translate(&self) -> mir::Expr {
        let kind = match &*self.kind {
            ExprKind::Variable(_) => unimplemented!(),
            ExprKind::Nil => unimplemented!(),
            ExprKind::Int(n) => mir::ExprKind::Int(*n),
            ExprKind::Float(f) => mir::ExprKind::Float(f.clone()),
            ExprKind::Bool(b) => mir::ExprKind::Bool(*b),
            ExprKind::Str(s) => mir::ExprKind::String(s.clone()),
            ExprKind::Array(arr) => {
                mir::ExprKind::Array(arr.iter().map(|e| e.translate().into()).collect())
            }
            ExprKind::AnonymousFunction(_, _, _) => unimplemented!(),
            ExprKind::IfElse(cond, tbranch, ebranch) => mir::ExprKind::IfElse(
                cond.translate().into(),
                tbranch.translate().into(),
                ebranch.clone().map(|s| s.translate().into()),
            ),
            ExprKind::Match(_, _) => unimplemented!(),
            ExprKind::Block(stmts) => {
                mir::ExprKind::Block(stmts.iter().map(|e| e.translate()).collect())
            }
            ExprKind::BinOp(_, _, _) => unimplemented!(),
            ExprKind::Unop(_, _) => unimplemented!(),
            ExprKind::FuncCall(_, _) => unimplemented!(),
            ExprKind::Tuple(elems) => {
                mir::ExprKind::Tuple(elems.iter().map(|e| e.translate().into()).collect())
            }
            ExprKind::MemberAccess(_, _) => unimplemented!(),
            ExprKind::MemberAccessLeadingDot(_) => unimplemented!(),
            ExprKind::IndexAccess(_, _) => unimplemented!(),
            ExprKind::Unwrap(_) => unimplemented!(),
            ExprKind::Try(_) => unimplemented!(),
            ExprKind::TaskBlock(_) => unimplemented!(),
        };

        mir::Expr {
            kind,
            span: self.loc.clone(),
            id: NodeId::new(),
        }
    }
}

impl Pat {
    fn translate(&self) -> mir::Pat {
        let kind = match &*self.kind {
            PatKind::Wildcard => mir::PatKind::Wildcard,
            PatKind::Binding(s) => mir::PatKind::Binding(s.clone()),
            PatKind::Variant(_, _, _) => unimplemented!(),
            PatKind::Void => mir::PatKind::Void,
            PatKind::Int(n) => mir::PatKind::Int(*n),
            PatKind::Float(f) => mir::PatKind::Float(f.clone()),
            PatKind::Bool(b) => mir::PatKind::Bool(*b),
            PatKind::Str(s) => mir::PatKind::Str(s.clone()),
            PatKind::Tuple(elems) => {
                mir::PatKind::Tuple(elems.iter().map(|p| p.translate().into()).collect())
            }
            PatKind::Struct(_, _) => unimplemented!(),
            PatKind::Or(_, _) => unimplemented!(),
        };

        mir::Pat {
            kind,
            span: self.loc.clone(),
        }
    }
}
