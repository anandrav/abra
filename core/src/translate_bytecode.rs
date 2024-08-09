use crate::assembly::{remove_labels, Instr, InstrOrLabel, Label};
use crate::ast::{NodeId, PatAnnotated, Toplevel};
use crate::operators::BinOpcode;
use crate::vm::Instr as VmInstr;
use crate::{
    ast::{Expr, ExprKind, NodeMap, Pat, PatKind, Stmt, StmtKind},
    statics::InferenceContext,
};
use std::collections::{HashMap, HashSet};
use std::f32::consts::E;
use std::rc::Rc;

#[derive(Debug)]
pub(crate) struct Translator {
    inf_ctx: InferenceContext,
    node_map: NodeMap,
    toplevels: Vec<Rc<Toplevel>>,
}

impl Translator {
    pub(crate) fn new(
        inf_ctx: InferenceContext,
        node_map: NodeMap,
        toplevels: Vec<Rc<Toplevel>>,
    ) -> Self {
        Self {
            inf_ctx,
            node_map,
            toplevels,
        }
    }

    pub(crate) fn translate(&self) -> Vec<VmInstr> {
        let mut instructions: Vec<InstrOrLabel> = vec![];

        // Map from name of local variable to its index in the stack
        // Since different types of values take up the same size, different variables with the same name can share the same slot
        let mut locals: HashMap<String, usize> = HashMap::new();

        for toplevel in self.toplevels.iter() {
            for statement in toplevel.statements.iter() {
                if let StmtKind::Let(_, pat, _) = &*statement.stmtkind {
                    collect_locals_from_let_pat(pat.0.clone(), &mut locals);
                }
            }
        }

        for i in 0..locals.len() {
            instructions.push(InstrOrLabel::Instr(Instr::PushNil));
        }
        for toplevel in self.toplevels.iter() {
            for (i, statement) in toplevel.statements.iter().enumerate() {
                match &*statement.stmtkind {
                    StmtKind::Let(_, pat, expr) => {
                        self.translate_expr(expr.clone(), &mut instructions);
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                    }
                    StmtKind::Expr(expr) => {
                        let is_last = i == toplevel.statements.len() - 1;
                        self.translate_expr(expr.clone(), &mut instructions);
                        if !is_last {
                            instructions.push(InstrOrLabel::Instr(Instr::Pop));
                        }
                    }
                    _ => {}
                }
            }
        }

        let instructions: Vec<VmInstr> = remove_labels(instructions);

        instructions
    }

    fn translate_expr(&self, expr: Rc<Expr>, instructions: &mut Vec<InstrOrLabel>) {
        match &*expr.exprkind {
            ExprKind::Int(i) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushInt(*i)));
            }
            ExprKind::BinOp(left, op, right) => {
                self.translate_expr(left.clone(), instructions);
                self.translate_expr(right.clone(), instructions);
                match op {
                    BinOpcode::Add => instructions.push(InstrOrLabel::Instr(Instr::Add)),
                    BinOpcode::Subtract => instructions.push(InstrOrLabel::Instr(Instr::Sub)),
                    BinOpcode::Multiply => instructions.push(InstrOrLabel::Instr(Instr::Mul)),
                    BinOpcode::Divide => instructions.push(InstrOrLabel::Instr(Instr::Div)),
                    _ => unimplemented!(),
                }
            }
            _ => unimplemented!(),
        }
    }
}

fn collect_locals_from_let_pat(pat: Rc<Pat>, locals: &mut HashMap<String, usize>) {
    match &*pat.patkind {
        PatKind::Var(symbol) => {
            locals.insert(symbol.clone(), locals.len());
        }
        PatKind::Tuple(pats) => {
            for pat in pats {
                collect_locals_from_let_pat(pat.clone(), locals);
            }
        }
        PatKind::Variant(_, Some(inner)) => {
            collect_locals_from_let_pat(inner.clone(), locals);
        }
        PatKind::Variant(_, None) => {}
        PatKind::Unit
        | PatKind::Bool(..)
        | PatKind::Int(..)
        | PatKind::Float(..)
        | PatKind::Str(..)
        | PatKind::Wildcard => {}
    }
}
