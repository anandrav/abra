use crate::ast::{
    Expr, ExprKind, FileAst, FuncDef, ItemKind, NodeId, Pat, PatKind, Stmt, StmtKind,
};
use crate::environment::Environment;
use crate::mir;
use crate::statics::{FuncResolutionKind, PolytypeDeclaration, StaticsContext, Type};
use std::rc::Rc;
use utils::id_set::IdSet;

pub(crate) struct Translator {
    statics: StaticsContext,
    file_asts: Vec<Rc<FileAst>>,
}

#[derive(Debug, Default)]
pub(crate) struct TranslatorState {
    funcs_to_generate: IdSet<FuncDesc>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
struct FuncDesc {
    kind: FuncKind,
    overload_ty: Option<Type>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
enum FuncKind {
    NamedFunc(Rc<FuncDef>),
}

type MonomorphEnv = Environment<PolytypeDeclaration, Type>;

impl Translator {
    pub(crate) fn new(statics: StaticsContext, file_asts: Vec<Rc<FileAst>>) -> Self {
        Self { statics, file_asts }
    }

    pub(crate) fn translate(&self) -> mir::Program {
        let mut funcs = vec![];

        // main function
        if let Some(main_ast) = self.file_asts.first() {
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
                    ItemKind::Stmt(stmt) => stmts.push(self.translate_stmt(stmt)),
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

    fn translate_stmt(&self, stmt: &Rc<Stmt>) -> mir::Stmt {
        let kind = match &*stmt.kind {
            StmtKind::Let(_, _, _) => unimplemented!(),
            StmtKind::Assign(_, _, _) => unimplemented!(),
            StmtKind::Expr(expr) => mir::StmtKind::Expr(self.translate_expr(expr).into()),
            StmtKind::Continue => mir::StmtKind::Continue,
            StmtKind::Break => mir::StmtKind::Break,
            StmtKind::Return(expr) => unimplemented!(),

            StmtKind::WhileLoop(_, _) => unimplemented!(),
            StmtKind::ForLoop(_, _, _) => unimplemented!(),
        };

        mir::Stmt {
            kind,
            span: stmt.loc.clone(),
        }
    }

    fn translate_expr(&self, expr: &Rc<Expr>) -> mir::Expr {
        let kind = match &*expr.kind {
            ExprKind::Variable(_) => unimplemented!(),
            ExprKind::Nil => unimplemented!(),
            ExprKind::Int(n) => mir::ExprKind::Int(*n),
            ExprKind::Float(f) => mir::ExprKind::Float(f.clone()),
            ExprKind::Bool(b) => mir::ExprKind::Bool(*b),
            ExprKind::Str(s) => mir::ExprKind::String(s.clone()),
            ExprKind::Array(arr) => unimplemented!(),
            ExprKind::AnonymousFunction(_, _, _) => unimplemented!(),
            ExprKind::IfElse(cond, tbranch, ebranch) => unimplemented!(),
            ExprKind::Match(_, _) => unimplemented!(),
            ExprKind::Block(stmts) => {
                mir::ExprKind::Block(stmts.iter().map(|s| self.translate_stmt(s)).collect())
            }
            ExprKind::BinOp(_, _, _) => unimplemented!(),
            ExprKind::Unop(_, _) => unimplemented!(),
            ExprKind::FuncCall(expr, args) => {
                //let args = args.iter().map(|e| self.translate_expr(e).into()).collect();
                unimplemented!()
            }
            ExprKind::Tuple(elems) => unimplemented!(),
            ExprKind::MemberAccess(_, _) => unimplemented!(),
            ExprKind::MemberAccessLeadingDot(_) => unimplemented!(),
            ExprKind::IndexAccess(_, _) => unimplemented!(),
            ExprKind::Unwrap(_) => unimplemented!(),
            ExprKind::Try(_) => unimplemented!(),
            ExprKind::TaskBlock(_) => unimplemented!(),
        };

        mir::Expr {
            kind,
            span: expr.loc.clone(),
            id: NodeId::new(),
        }
    }

    fn translate_pat(&self, pat: &Rc<Pat>) -> mir::Pat {
        let kind = match &*pat.kind {
            PatKind::Wildcard => mir::PatKind::Wildcard,
            PatKind::Binding(s) => mir::PatKind::Binding(s.clone()),
            PatKind::Variant(_, _, _) => unimplemented!(),
            PatKind::Void => mir::PatKind::Void,
            PatKind::Int(n) => mir::PatKind::Int(*n),
            PatKind::Float(f) => mir::PatKind::Float(f.clone()),
            PatKind::Bool(b) => mir::PatKind::Bool(*b),
            PatKind::Str(s) => mir::PatKind::Str(s.clone()),
            PatKind::Tuple(elems) => mir::PatKind::Tuple(
                elems
                    .iter()
                    .map(|p| self.translate_pat(pat).into())
                    .collect(),
            ),
            PatKind::Struct(_, _) => unimplemented!(),
            PatKind::Or(_, _) => unimplemented!(),
        };

        mir::Pat {
            kind,
            span: pat.loc.clone(),
        }
    }
}
