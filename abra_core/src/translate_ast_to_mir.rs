use crate::ast::{
    AstNode, Expr, ExprKind, FileAst, FuncDef, ItemKind, NodeId, Pat, PatKind, Stmt, StmtKind,
};
use crate::environment::Environment;
use crate::mir;
use crate::statics::{Declaration, FuncResolutionKind, PolytypeDeclaration, StaticsContext, Type};
use crate::translate_helpers::*;
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

impl Translator {
    pub(crate) fn new(statics: StaticsContext, file_asts: Vec<Rc<FileAst>>) -> Self {
        Self { statics, file_asts }
    }

    pub(crate) fn translate(&self) -> mir::Program {
        let mut st = &mut TranslatorState::default();
        let mono = MonomorphEnv::empty();
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
                    ItemKind::Stmt(stmt) => stmts.push(self.translate_stmt(stmt, st, &mono)),
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

    fn get_ty(&self, mono: &MonomorphEnv, node: AstNode) -> Option<Type> {
        self.statics.solution_of_node(node).map(|t| t.subst(mono))
    }

    fn translate_stmt(
        &self,
        stmt: &Rc<Stmt>,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
    ) -> mir::Stmt {
        let kind = match &*stmt.kind {
            StmtKind::Let(_, _, _) => unimplemented!(),
            StmtKind::Assign(_, _, _) => unimplemented!(),
            StmtKind::Expr(expr) => mir::StmtKind::Expr(self.translate_expr(expr, st, mono).into()),
            StmtKind::Continue => mir::StmtKind::Continue,
            StmtKind::Break => mir::StmtKind::Break,
            StmtKind::Return(_expr) => unimplemented!(),

            StmtKind::WhileLoop(_, _) => unimplemented!(),
            StmtKind::ForLoop(_, _, _) => unimplemented!(),
        };

        mir::Stmt {
            kind,
            span: stmt.loc.clone(),
        }
    }

    fn translate_expr(
        &self,
        expr: &Rc<Expr>,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
    ) -> mir::Expr {
        let kind = match &*expr.kind {
            ExprKind::Variable(_) => unimplemented!(),
            ExprKind::Nil => unimplemented!(),
            ExprKind::Int(n) => mir::ExprKind::Int(*n),
            ExprKind::Float(f) => mir::ExprKind::Float(f.clone()),
            ExprKind::Bool(b) => mir::ExprKind::Bool(*b),
            ExprKind::Str(s) => mir::ExprKind::String(s.clone()),
            ExprKind::Array(_arr) => unimplemented!(),
            ExprKind::AnonymousFunction(_, _, _) => unimplemented!(),
            ExprKind::IfElse(_cond, _tbranch, _ebranch) => unimplemented!(),
            ExprKind::Match(_, _) => unimplemented!(),
            ExprKind::Block(stmts) => mir::ExprKind::Block(
                stmts
                    .iter()
                    .map(|s| self.translate_stmt(s, st, mono))
                    .collect(),
            ),
            ExprKind::BinOp(_, _, _) => unimplemented!(),
            ExprKind::Unop(_, _) => unimplemented!(),
            ExprKind::FuncCall(func, args) => match &*expr.kind {
                ExprKind::Variable(_) => {
                    let decl = &self.statics.resolution_map[&func.id];
                    let args: Vec<mir::Expr> = if let Some(reordered_args) =
                        self.statics.function_call_arg_order.get(&func.id).cloned()
                    {
                        reordered_args
                            .iter()
                            .map(|e| self.translate_expr(e, st, mono))
                            .collect()
                    } else {
                        args.iter()
                            .map(|e| self.translate_expr(&e.val, st, mono))
                            .collect()
                    };
                    let id = self.translate_func_call(decl, func.node(), mono, st);
                    mir::ExprKind::FuncCall(id, args)
                }
                _ => unimplemented!(),
            },
            ExprKind::Tuple(_elems) => unimplemented!(),
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

    fn translate_func_call(
        &self,
        decl: &Declaration,
        func_node: AstNode,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) -> u32 {
        match decl {
            Declaration::FreeFunction(FuncResolutionKind::Ordinary(f)) => {
                let f_fully_qualified_name = &self.statics.fully_qualified_names[&f.name.id];
                let id =
                    self.translate_func_call_helper(f, f_fully_qualified_name, func_node, mono, st);
                id
            }
            _ => unimplemented!(),
        }
    }

    fn translate_func_call_helper(
        &self,
        f: &Rc<FuncDef>,
        f_fully_qualified_name: &str,
        func_node: AstNode,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) -> u32 {
        let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
        let overload_ty = if !func_ty.is_overloaded() {
            None
        } else {
            Some(self.get_ty(mono, func_node).unwrap())
        };
        let id = st.funcs_to_generate.insert(FuncDesc {
            kind: FuncKind::NamedFunc(f.clone()),
            overload_ty,
        });
        id
    }

    fn translate_pat(&self, pat: &Rc<Pat>, st: &mut TranslatorState) -> mir::Pat {
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
                    .map(|_p| self.translate_pat(pat, st).into())
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
