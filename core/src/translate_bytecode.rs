use crate::assembly::{remove_labels, Instr, InstrOrLabel, Label};
use crate::ast::{NodeId, PatAnnotated, Toplevel};
use crate::operators::BinOpcode;
use crate::statics::Resolution;
use crate::vm::Instr as VmInstr;
use crate::EffectTrait;
use crate::{
    ast::{Expr, ExprKind, NodeMap, Pat, PatKind, Stmt, StmtKind},
    statics::InferenceContext,
};
use std::collections::{HashMap, HashSet};
use std::f32::consts::E;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

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

    pub(crate) fn translate<Effect: EffectTrait>(&self) -> (Vec<VmInstr>, Vec<String>) {
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
                let func_name_blacklist = [
                    "not", "range", "fold", "sum", "sumf", "max", "min", "clamp", "abs", "sqrt",
                    "concat", "map", "for_each", "filter", "reverse",
                ];
                // don't generate code for functions in prelude, not ready for that yet.
                if func_name_blacklist.contains(&func_name.as_str()) {
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

        // Create functions for effects
        let effect_list = Effect::enumerate();
        for (i, effect) in effect_list.iter().enumerate() {
            instructions.push(InstrOrLabel::Label(effect.function_name()));
            instructions.push(InstrOrLabel::Instr(Instr::Effect(i as u16)));
            instructions.push(InstrOrLabel::Instr(Instr::Return));
        }

        for instr in &instructions {
            println!("{}", instr);
        }
        let instructions = remove_labels(instructions, &self.inf_ctx.string_constants);
        let mut string_table: Vec<String> =
            vec!["".to_owned(); self.inf_ctx.string_constants.len()];
        dbg!(&self.inf_ctx.string_constants);
        for (s, idx) in self.inf_ctx.string_constants.iter() {
            string_table[*idx] = s.clone();
        }
        (instructions, string_table)
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
            ExprKind::Bool(b) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushBool(*b)));
            }
            ExprKind::Int(i) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushInt(*i)));
            }
            ExprKind::Str(s) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushString(s.clone())));
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
            ExprKind::If(cond, then_block, Some(else_block)) => {
                self.translate_expr(cond.clone(), locals, instructions);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                instructions.push(InstrOrLabel::Instr(Instr::JumpIf(then_label.clone())));
                self.translate_expr(else_block.clone(), locals, instructions);
                instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                instructions.push(InstrOrLabel::Label(then_label));
                self.translate_expr(then_block.clone(), locals, instructions);
                instructions.push(InstrOrLabel::Label(end_label));
            }
            ExprKind::If(cond, then_block, None) => {
                self.translate_expr(cond.clone(), locals, instructions);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                instructions.push(InstrOrLabel::Instr(Instr::JumpIf(then_label.clone())));
                instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                instructions.push(InstrOrLabel::Label(then_label));
                self.translate_expr(then_block.clone(), locals, instructions);
                instructions.push(InstrOrLabel::Label(end_label));
                instructions.push(InstrOrLabel::Instr(Instr::PushNil)); // TODO get rid of this
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
            StmtKind::Set(expr1, expr2) => match &*expr1.exprkind {
                ExprKind::Var(symbol) => {
                    let idx = locals.get(symbol).unwrap();
                    self.translate_expr(expr2.clone(), locals, instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(*idx)));
                }
                _ => unimplemented!(),
            },
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), locals, instructions);
                if !is_last {
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                }
            }
            StmtKind::FuncDef(_, _, _, _) => {
                // handled elsewhere
            }
            StmtKind::InterfaceDef(..) | StmtKind::TypeDef(..) => {
                // noop
            }
            StmtKind::InterfaceImpl(..) => {
                // TODO
            }
            _ => panic!("unimplemented: {:?}", stmt.stmtkind),
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

fn make_label(hint: &str) -> Label {
    if hint.contains(" ") {
        panic!("Label hint cannot contain spaces");
    }
    static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
    let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{}_{}", hint, id)
}
