use crate::assembly::{remove_labels, Instr, InstrOrLabel, Label};
use crate::ast::{NodeId, PatAnnotated, Toplevel};
use crate::operators::BinOpcode;
use crate::statics::Resolution;
use crate::vm::Instr as VmInstr;
use crate::{
    ast::{Expr, ExprKind, NodeMap, Pat, PatKind, Stmt, StmtKind},
    statics::InferenceContext,
};
use std::collections::{HashMap, HashSet};
use std::f32::consts::E;
use std::rc::Rc;

type Locals = HashMap<String, i32>;

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

        // Handle the main function (toplevels)
        let mut locals = Locals::new();
        for toplevel in self.toplevels.iter() {
            collect_locals_stmt(&toplevel.statements, &mut locals);
        }
        for i in 0..locals.len() {
            instructions.push(InstrOrLabel::Instr(Instr::PushNil));
        }
        for toplevel in self.toplevels.iter() {
            for (i, statement) in toplevel.statements.iter().enumerate() {
                self.translate_stmt(
                    statement.clone(),
                    i == toplevel.statements.len() - 1,
                    &locals,
                    &mut instructions,
                );
            }
        }
        instructions.push(InstrOrLabel::Instr(Instr::Stop));

        // Handle all other functions
        for toplevel in self.toplevels.iter() {
            if let StmtKind::FuncDef(name, args, _, body) = &*toplevel.statements[0].stmtkind {
                let func_name = name.patkind.get_identifier_of_variable();
                if func_name != "mk_pair" {
                    continue;
                }
                instructions.push(InstrOrLabel::Label(func_name));
                let mut locals = Locals::new();
                collect_locals_expr(body, &mut locals);
                let locals_count = locals.len();
                for i in 0..locals_count {
                    instructions.push(InstrOrLabel::Instr(Instr::PushNil));
                }
                for (i, arg) in args.iter().rev().enumerate() {
                    locals.insert(arg.0.patkind.get_identifier_of_variable(), -(i as i32) - 1);
                }
                self.translate_expr(body.clone(), &locals, &mut instructions);
                instructions.push(InstrOrLabel::Instr(Instr::Return));
                // unimplemented!();
            }
        }

        let instructions: Vec<VmInstr> = remove_labels(instructions);
        instructions
    }

    fn handle_binding(&self, pat: Rc<Pat>, locals: &Locals, instructions: &mut Vec<InstrOrLabel>) {
        match &*pat.patkind {
            PatKind::Var(symbol) => {
                let idx = locals.get(symbol).unwrap();
                instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(*idx)));
            }
            PatKind::Tuple(pats) => {
                instructions.push(InstrOrLabel::Instr(Instr::UnpackTuple));
                for pat in pats.iter().rev() {
                    self.handle_binding(pat.clone(), locals, instructions);
                }
            }
            PatKind::Variant(_, Some(inner)) => {
                unimplemented!();
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

    fn translate_expr(
        &self,
        expr: Rc<Expr>,
        locals: &Locals,
        instructions: &mut Vec<InstrOrLabel>,
    ) {
        match &*expr.exprkind {
            ExprKind::Var(symbol) => {
                let idx = locals.get(symbol).unwrap();
                instructions.push(InstrOrLabel::Instr(Instr::LoadOffset(*idx)));
            }
            ExprKind::Int(i) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushInt(*i)));
            }
            ExprKind::BinOp(left, op, right) => {
                self.translate_expr(left.clone(), locals, instructions);
                self.translate_expr(right.clone(), locals, instructions);
                match op {
                    BinOpcode::Add => instructions.push(InstrOrLabel::Instr(Instr::Add)),
                    BinOpcode::Subtract => instructions.push(InstrOrLabel::Instr(Instr::Sub)),
                    BinOpcode::Multiply => instructions.push(InstrOrLabel::Instr(Instr::Mul)),
                    BinOpcode::Divide => instructions.push(InstrOrLabel::Instr(Instr::Div)),
                    _ => unimplemented!(),
                }
            }
            ExprKind::FuncAp(func, args) => {
                if let ExprKind::Var(symbol) = &*func.exprkind {
                    for arg in args {
                        self.translate_expr(arg.clone(), locals, instructions);
                    }
                    let resolution = self.inf_ctx.name_resolutions.get(&func.id).unwrap();
                    match resolution {
                        Resolution::Node(node_id) => {
                            let node = self.node_map.get(node_id).unwrap();
                            let stmt = node.to_stmt().unwrap();
                            match &*stmt.stmtkind {
                                StmtKind::FuncDef(name, _, _, _) => {
                                    instructions.push(InstrOrLabel::Instr(Instr::Call(
                                        name.patkind.get_identifier_of_variable(),
                                        args.len() as u8,
                                    )));
                                    return;
                                }
                                _ => {
                                    unimplemented!();
                                }
                            }
                        }
                        Resolution::Builtin(_) => {
                            unimplemented!()
                        }
                    }
                }
                panic!("unimplemented: {:?}", expr.exprkind);
            }
            ExprKind::Block(statements) => {
                for (i, statement) in statements.iter().enumerate() {
                    self.translate_stmt(
                        statement.clone(),
                        i == statements.len() - 1,
                        locals,
                        instructions,
                    );
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), locals, instructions);
                }
                instructions.push(InstrOrLabel::Instr(Instr::MakeTuple(exprs.len() as u8)));
            }
            _ => panic!("unimplemented: {:?}", expr.exprkind),
        }
    }

    fn translate_stmt(
        &self,
        stmt: Rc<Stmt>,
        is_last: bool,
        locals: &Locals,
        instructions: &mut Vec<InstrOrLabel>,
    ) {
        match &*stmt.stmtkind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr.clone(), locals, instructions);
                self.handle_binding(pat.0.clone(), locals, instructions);
            }
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), locals, instructions);
                if !is_last {
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                }
            }
            _ => {}
        }
    }
}

fn collect_locals_expr(expr: &Expr, locals: &mut Locals) {
    match &*expr.exprkind {
        ExprKind::Block(statements) => {
            for statement in statements {
                collect_locals_stmt(&[statement.clone()], locals);
            }
        }
        _ => {}
    }
}

fn collect_locals_stmt(statements: &[Rc<Stmt>], locals: &mut Locals) {
    for statement in statements {
        match &*statement.stmtkind {
            StmtKind::Let(_, pat, _) => {
                collect_locals_from_let_pat(pat.0.clone(), locals);
            }
            _ => {}
        }
    }
}

fn collect_locals_from_let_pat(pat: Rc<Pat>, locals: &mut Locals) {
    match &*pat.patkind {
        PatKind::Var(symbol) => {
            locals.insert(symbol.clone(), locals.len() as i32);
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
