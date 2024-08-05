use crate::ast::{NodeId, PatAnnotated, Toplevel};
use crate::operators::BinOpcode;
use crate::vm::Instr as VmInstr;
use crate::vm::Opcode;
use crate::{
    ast::{Expr, ExprKind, NodeMap, Pat, PatKind, Stmt, StmtKind},
    statics::InferenceContext,
};
use std::collections::HashMap;
use std::f32::consts::E;
use std::rc::Rc;

type Local = (String, NodeId);

type Label = String;

#[derive(Debug)]
enum InstrOrLabel {
    Instr(Instr),
    Label(Label),
}

#[derive(Debug)]
enum Instr {
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Return,
    PushBool(bool),
    PushInt(i64),
    Jump(Label),
    JumpIfTrue(Label),
    Call(Label),
}

impl Instr {
    fn opcode(&self) -> Opcode {
        match self {
            Instr::Pop => Opcode::Pop,
            Instr::Add => Opcode::Add,
            Instr::Sub => Opcode::Sub,
            Instr::Mul => Opcode::Mul,
            Instr::Div => Opcode::Div,
            Instr::Return => Opcode::Return,
            Instr::PushBool(_) => Opcode::PushBool,
            Instr::PushInt(_) => Opcode::PushInt,
            Instr::Jump(_) => Opcode::Jump,
            Instr::JumpIfTrue(_) => Opcode::JumpIfTrue,
            Instr::Call(_) => Opcode::Call,
        }
    }
}

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

    pub(crate) fn translate(&self) -> Vec<u8> {
        let mut instructions: Vec<InstrOrLabel> = vec![];

        let mut locals = vec![];

        for toplevel in self.toplevels.iter() {
            for statement in toplevel.statements.iter() {
                if let StmtKind::Let(_, pat, _) = &*statement.stmtkind {
                    self.collect_locals_from_let_pat(pat.0.clone(), &mut locals);
                }
            }
        }

        for toplevel in self.toplevels.iter() {
            for (i, statement) in toplevel.statements.iter().enumerate() {
                match &*statement.stmtkind {
                    StmtKind::Let(_, pat, expr) => {
                        let expr = self.translate_expr(expr.clone(), &mut instructions);
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                    }
                    StmtKind::Expr(expr) => {
                        let is_last = i == toplevel.statements.len() - 1;
                        let expr = self.translate_expr(expr.clone(), &mut instructions);
                        if !is_last {
                            instructions.push(InstrOrLabel::Instr(Instr::Pop));
                        }
                    }
                    _ => {}
                }
            }
        }

        let instructions: Vec<VmInstr> = remove_labels(instructions);
        dbg!(&instructions);
        let mut bytecode: Vec<u8> = vec![];
        for instr in instructions {
            instr.encode(&mut bytecode);
        }

        println!("{}", bytecode.len());

        bytecode
    }

    fn collect_locals_from_let_pat(&self, pat: Rc<Pat>, locals: &mut Vec<Local>) {
        match &*pat.patkind {
            PatKind::Var(symbol) => {
                locals.push((symbol.clone(), pat.id));
            }
            PatKind::Tuple(pats) => {
                for pat in pats {
                    self.collect_locals_from_let_pat(pat.clone(), locals);
                }
            }
            PatKind::Variant(_, Some(inner)) => {
                self.collect_locals_from_let_pat(inner.clone(), locals);
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
                    _ => unimplemented!(),
                }
            }
            _ => unimplemented!(),
        }
    }
}

fn remove_labels(items: Vec<InstrOrLabel>) -> Vec<VmInstr> {
    let mut ret: Vec<VmInstr> = vec![];
    let mut offset = 0;
    let mut label_to_idx: HashMap<Label, usize> = HashMap::new();
    for item in items.iter() {
        match item {
            InstrOrLabel::Instr(instr) => {
                offset += instr.opcode().nbytes();
            }
            InstrOrLabel::Label(label) => {
                label_to_idx.insert(label.clone(), offset);
            }
        }
    }

    for item in items {
        if let InstrOrLabel::Instr(instr) = item {
            ret.push(instr_to_vminstr(instr, &label_to_idx));
        }
    }

    ret
}

fn get_label(s: &str) -> Option<String> {
    if s.ends_with(":") {
        Some(s[0..s.len() - 1].to_owned())
    } else {
        None
    }
}

fn instr_to_vminstr(instr: Instr, label_to_idx: &HashMap<Label, usize>) -> VmInstr {
    match instr {
        Instr::Pop => VmInstr::Pop,
        Instr::Add => VmInstr::Add,
        Instr::Sub => VmInstr::Sub,
        Instr::Mul => VmInstr::Mul,
        Instr::Div => VmInstr::Div,
        Instr::Return => VmInstr::Return,
        Instr::PushBool(b) => VmInstr::PushBool(b),
        Instr::PushInt(i) => VmInstr::PushInt(i),
        Instr::Jump(label) => VmInstr::Jump(label_to_idx[&label]),
        Instr::JumpIfTrue(label) => VmInstr::JumpIfTrue(label_to_idx[&label]),
        Instr::Call(label) => VmInstr::Call(label_to_idx[&label]),
    }
}
