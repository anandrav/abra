use crate::assembly::{remove_labels, Instr, InstrOrLabel, Label};
use crate::ast::{NodeId, Sources, Toplevel, TypeDefKind};
use crate::operators::BinOpcode;
use crate::statics::{Resolution, SolvedType};
use crate::vm::{AbraInt, Instr as VmInstr};
use crate::EffectTrait;
use crate::{
    ast::{Expr, ExprKind, NodeMap, Pat, PatKind, Stmt, StmtKind},
    statics::InferenceContext,
};
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

type Locals = HashMap<NodeId, i32>;

#[derive(Debug)]
pub(crate) struct Translator {
    inf_ctx: InferenceContext,
    node_map: NodeMap,
    sources: Sources,
    toplevels: Vec<Rc<Toplevel>>,
}

impl Translator {
    pub(crate) fn new(
        inf_ctx: InferenceContext,
        node_map: NodeMap,
        sources: Sources,
        toplevels: Vec<Rc<Toplevel>>,
    ) -> Self {
        Self {
            inf_ctx,
            node_map,
            sources,
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
        dbg!(&locals);
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
            for statement in &toplevel.statements {
                if let StmtKind::FuncDef(name, args, _, body) = &*statement.stmtkind {
                    let func_name = name.patkind.get_identifier_of_variable();
                    let func_name_blacklist = [
                        "not", "range", "fold", "sum", "sumf", "max", "min", "clamp", "abs",
                        "sqrt", "concat", "map", "for_each", "filter", "reverse", "print",
                        "println",
                    ];
                    // don't generate code for functions in prelude, not ready for that yet.
                    if func_name_blacklist.contains(&func_name.as_str()) {
                        continue;
                    }
                    println!("Generating code for function: {}", func_name);
                    instructions.push(InstrOrLabel::Label(func_name));
                    let mut locals = Locals::new();
                    collect_locals_expr(body, &mut locals);
                    let locals_count = locals.len();
                    for i in 0..locals_count {
                        instructions.push(InstrOrLabel::Instr(Instr::PushNil));
                    }
                    for (i, arg) in args.iter().rev().enumerate() {
                        locals.entry(arg.0.id).or_insert(-(i as i32) - 1);
                    }
                    self.translate_expr(body.clone(), &locals, &mut instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::Return));
                    // unimplemented!();
                }
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

    fn translate_expr(
        &self,
        expr: Rc<Expr>,
        locals: &Locals,
        instructions: &mut Vec<InstrOrLabel>,
    ) {
        match &*expr.exprkind {
            ExprKind::Var(symbol) => {
                // adt variant
                match self.inf_ctx.name_resolutions.get(&expr.id).unwrap() {
                    Resolution::Variant(node_id, variant_name) => {
                        let node = self.node_map.get(node_id).unwrap();
                        let stmt = node.to_stmt().unwrap();
                        match &*stmt.stmtkind {
                            StmtKind::TypeDef(kind) => match &**kind {
                                TypeDefKind::Adt(_, _, variants) => {
                                    let tag = variants
                                        .iter()
                                        .position(|v| v.ctor == *variant_name)
                                        .expect("variant not found")
                                        as u16;
                                    instructions.push(InstrOrLabel::Instr(
                                        Instr::ConstructVariant { tag, nargs: 0 },
                                    ));
                                }
                                _ => panic!("unexpected stmt: {:?}", stmt.stmtkind),
                            },
                            _ => panic!("unexpected stmt: {:?}", stmt.stmtkind),
                        }
                    }
                    Resolution::Node(node_id) => {
                        let span = self.node_map.get(node_id).unwrap().span();
                        let mut s = String::new();
                        span.display(
                            &mut s,
                            &self.sources,
                            &format!("symbol {} resolved to", symbol),
                        );
                        println!("{}", s);
                        let idx = locals.get(node_id).unwrap();
                        instructions.push(InstrOrLabel::Instr(Instr::LoadOffset(*idx)));
                    }
                    Resolution::Builtin(s) => {
                        unimplemented!()
                    }
                }
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
                    _ => panic!("op not implemented: {:?}", op),
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
                                }
                                StmtKind::TypeDef(kind) => match &**kind {
                                    TypeDefKind::Struct(_, _, fields) => {
                                        instructions.push(InstrOrLabel::Instr(Instr::Construct(
                                            fields.len() as u16,
                                        )));
                                    }
                                    _ => unimplemented!(),
                                },
                                _ => panic!("unexpected stmt: {:?}", stmt.stmtkind),
                            }
                        }
                        Resolution::Variant(node_id, variant_name) => {
                            let node = self.node_map.get(node_id).unwrap();
                            let stmt = node.to_stmt().unwrap();
                            match &*stmt.stmtkind {
                                StmtKind::TypeDef(kind) => match &**kind {
                                    TypeDefKind::Adt(_, _, variants) => {
                                        let tag = variants
                                            .iter()
                                            .position(|v| v.ctor == *variant_name)
                                            .expect("variant not found")
                                            as u16;
                                        instructions.push(InstrOrLabel::Instr(
                                            Instr::ConstructVariant {
                                                tag,
                                                nargs: args.len() as u16,
                                            },
                                        ));
                                    }
                                    _ => panic!("unexpected stmt: {:?}", stmt.stmtkind),
                                },
                                _ => panic!("unexpected stmt: {:?}", stmt.stmtkind),
                            }
                        }
                        Resolution::Builtin(s) => {
                            // TODO use an enum instead of strings
                            match s.as_str() {
                                "print_string" => {
                                    // TODO differentiate between a builtin Effect like print_string() and a user-customized Effect like impulse()
                                    instructions.push(InstrOrLabel::Instr(Instr::Effect(0)));
                                }
                                _ => panic!("unrecognized builtin: {}", s),
                            }
                        }
                    }
                } else {
                    panic!("unimplemented: {:?}", expr.exprkind)
                }
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
                instructions.push(InstrOrLabel::Instr(Instr::Construct(exprs.len() as u16)));
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
            ExprKind::FieldAccess(accessed, field) => {
                // TODO, this downcast shouldn't be necessary
                let ExprKind::Var(field_name) = &*field.exprkind else {
                    panic!()
                };
                self.translate_expr(accessed.clone(), locals, instructions);
                let idx = idx_of_field(&self.inf_ctx, accessed.clone(), field_name);
                instructions.push(InstrOrLabel::Instr(Instr::GetField(idx)));
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), locals, instructions);
                }
                instructions.push(InstrOrLabel::Instr(Instr::Construct(exprs.len() as u16)));
            }
            ExprKind::IndexAccess(array, index) => {
                self.translate_expr(index.clone(), locals, instructions);
                self.translate_expr(array.clone(), locals, instructions);
                instructions.push(InstrOrLabel::Instr(Instr::GetIdx));
            }
            ExprKind::Match(expr, arms) => {
                let ty = self.inf_ctx.solution_of_node(expr.id).unwrap();

                self.translate_expr(expr.clone(), locals, instructions);
                let end_label = make_label("endmatch");
                // Check scrutinee against each arm's pattern
                let arm_labels = arms
                    .iter()
                    .enumerate()
                    .map(|(i, _)| make_label(&format!("arm{}", i)))
                    .collect::<Vec<_>>();
                for (i, arm) in arms.iter().enumerate() {
                    let arm_label = arm_labels[i].clone();

                    self.translate_pat_comparison(&ty, arm.pat.clone(), instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::JumpIf(arm_label)));
                }
                for (i, arm) in arms.iter().enumerate() {
                    instructions.push(InstrOrLabel::Label(arm_labels[i].clone()));
                    // pop the scrutinee
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                    self.translate_expr(arm.expr.clone(), locals, instructions);
                    if i != arms.len() - 1 {
                        instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                    }
                }
                instructions.push(InstrOrLabel::Label(end_label));
            }
            _ => panic!("unimplemented: {:?}", expr.exprkind),
        }
    }

    // emit instructions for checking if a pattern matches the TOS, yielding a boolean
    fn translate_pat_comparison(
        &self,
        scrutinee_ty: &SolvedType,
        pat: Rc<Pat>,
        instructions: &mut Vec<InstrOrLabel>,
    ) {
        match &*pat.patkind {
            PatKind::Wildcard | PatKind::Var(_) | PatKind::Unit => {
                instructions.push(InstrOrLabel::Instr(Instr::PushBool(true)));
                return;
            }
            _ => {}
        }

        // duplicate the scrutinee before doing a comparison
        instructions.push(InstrOrLabel::Instr(Instr::Duplicate));

        match scrutinee_ty {
            SolvedType::Int => match &*pat.patkind {
                PatKind::Int(i) => {
                    instructions.push(InstrOrLabel::Instr(Instr::PushInt(*i)));
                    instructions.push(InstrOrLabel::Instr(Instr::Equal));
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            SolvedType::Bool => match &*pat.patkind {
                PatKind::Bool(b) => {
                    instructions.push(InstrOrLabel::Instr(Instr::PushBool(*b)));
                    instructions.push(InstrOrLabel::Instr(Instr::Equal));
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            SolvedType::UdtInstance(symbol, _) => match &*pat.patkind {
                PatKind::Variant(ctor, None) => {
                    let adt = self.inf_ctx.adt_defs.get(symbol).unwrap();
                    let tag = adt
                        .variants
                        .iter()
                        .position(|v| v.ctor == *ctor)
                        .expect("variant not found") as u16;
                    instructions.push(InstrOrLabel::Instr(Instr::Deconstruct));
                    instructions.push(InstrOrLabel::Instr(Instr::PushInt(tag as AbraInt)));
                    instructions.push(InstrOrLabel::Instr(Instr::Equal));
                }
                PatKind::Variant(ctor, Some(inner)) => {
                    let adt = self.inf_ctx.adt_defs.get(symbol).unwrap();
                    let tag_fail_label = make_label("tag_fail");
                    let end_label = make_label("endvariant");

                    let tag = adt
                        .variants
                        .iter()
                        .position(|v| v.ctor == *ctor)
                        .expect("variant not found") as u16;
                    let arity = match adt.variants[tag as usize].data.solution().unwrap() {
                        SolvedType::Tuple(types) => types.len(),
                        _ => 1,
                    };
                    instructions.push(InstrOrLabel::Instr(Instr::Deconstruct));
                    instructions.push(InstrOrLabel::Instr(Instr::PushInt(tag as AbraInt)));
                    instructions.push(InstrOrLabel::Instr(Instr::Equal));
                    instructions.push(InstrOrLabel::Instr(Instr::Not));
                    instructions.push(InstrOrLabel::Instr(Instr::JumpIf(tag_fail_label.clone())));

                    let inner_ty = self.inf_ctx.solution_of_node(inner.id).unwrap();
                    self.translate_pat_comparison(&inner_ty, inner.clone(), instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));

                    // FAILURE
                    instructions.push(InstrOrLabel::Label(tag_fail_label));
                    for _ in 0..arity {
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                    }
                    instructions.push(InstrOrLabel::Instr(Instr::PushBool(false)));

                    instructions.push(InstrOrLabel::Label(end_label));
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            SolvedType::Tuple(types) => match &*pat.patkind {
                PatKind::Tuple(pats) => {
                    let final_element_success_label = make_label("tuple_success");
                    let end_label = make_label("endtuple");
                    // spill tuple elements onto stack
                    instructions.push(InstrOrLabel::Instr(Instr::Deconstruct));
                    // for each element of tuple pattern, compare to TOS
                    // if the comparison fails, pop all remaining tuple elements and jump to the next arm
                    // if it makes it through each tuple element, jump to the arm's expression
                    let failure_labels = (0..pats.len())
                        .map(|_| make_label("tuple_fail"))
                        .collect::<Vec<_>>();
                    for (i, pat) in pats.iter().enumerate() {
                        let ty = &types[i];
                        self.translate_pat_comparison(ty, pat.clone(), instructions);
                        let is_last = i == pats.len() - 1;
                        instructions.push(InstrOrLabel::Instr(Instr::Not));
                        instructions.push(InstrOrLabel::Instr(Instr::JumpIf(
                            failure_labels[i].clone(),
                        )));
                        // SUCCESS
                        // pop the tuple element so we can compare the next one
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                        if is_last {
                            instructions.push(InstrOrLabel::Instr(Instr::Jump(
                                final_element_success_label.clone(),
                            )));
                        }
                    }
                    // SUCCESS CASE
                    instructions.push(InstrOrLabel::Label(final_element_success_label));
                    instructions.push(InstrOrLabel::Instr(Instr::PushBool(true)));
                    instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));

                    // FAILURE CASE
                    // clean up the remaining tuple elements before yielding false
                    for label in failure_labels {
                        instructions.push(InstrOrLabel::Label(label));
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                    }
                    instructions.push(InstrOrLabel::Instr(Instr::PushBool(false)));

                    instructions.push(InstrOrLabel::Label(end_label));
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            _ => unimplemented!(),
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
                self.handle_let_binding(pat.0.clone(), locals, instructions);
            }
            StmtKind::Set(expr1, rvalue) => match &*expr1.exprkind {
                ExprKind::Var(_) => {
                    let Resolution::Node(node_id) =
                        self.inf_ctx.name_resolutions.get(&expr1.id).unwrap()
                    else {
                        panic!("expected variableto be defined in node");
                    };
                    let idx = locals.get(node_id).unwrap();
                    self.translate_expr(rvalue.clone(), locals, instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(*idx)));
                }
                ExprKind::FieldAccess(accessed, field) => {
                    // TODO, this downcast shouldn't be necessary
                    let ExprKind::Var(field_name) = &*field.exprkind else {
                        panic!()
                    };
                    self.translate_expr(rvalue.clone(), locals, instructions);
                    self.translate_expr(accessed.clone(), locals, instructions);
                    let idx = idx_of_field(&self.inf_ctx, accessed.clone(), field_name);
                    instructions.push(InstrOrLabel::Instr(Instr::SetField(idx)));
                }
                ExprKind::IndexAccess(array, index) => {
                    self.translate_expr(rvalue.clone(), locals, instructions);
                    self.translate_expr(index.clone(), locals, instructions);
                    self.translate_expr(array.clone(), locals, instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::SetIdx));
                }
                _ => unimplemented!(),
            },
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), locals, instructions);
                if !is_last {
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                }
            }
            StmtKind::InterfaceImpl(..) => {
                // TODO
            }
            StmtKind::FuncDef(_, _, _, _) => {
                // noop -- handled elsewhere
            }
            StmtKind::InterfaceDef(..) | StmtKind::TypeDef(..) => {
                // noop
            }
        }
    }

    fn handle_let_binding(
        &self,
        pat: Rc<Pat>,
        locals: &Locals,
        instructions: &mut Vec<InstrOrLabel>,
    ) {
        match &*pat.patkind {
            PatKind::Var(_) => {
                let idx = locals.get(&pat.id).unwrap();
                instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(*idx)));
            }
            PatKind::Tuple(pats) => {
                instructions.push(InstrOrLabel::Instr(Instr::Deconstruct));
                for pat in pats.iter() {
                    self.handle_let_binding(pat.clone(), locals, instructions);
                }
            }
            PatKind::Variant(_, _) => {}
            PatKind::Unit
            | PatKind::Bool(..)
            | PatKind::Int(..)
            | PatKind::Float(..)
            | PatKind::Str(..)
            | PatKind::Wildcard => {}
        }
    }
}

enum PatComparisonStrategy {
    OnFail,
    OnSuccess,
}

fn collect_locals_expr(expr: &Expr, locals: &mut Locals) {
    match &*expr.exprkind {
        ExprKind::Block(statements) => {
            for statement in statements {
                collect_locals_stmt(&[statement.clone()], locals);
            }
        }
        ExprKind::Match(_, arms) => {
            for arm in arms {
                collect_locals_pat(arm.pat.clone(), locals);
                collect_locals_expr(&arm.expr, locals);
            }
        }
        _ => {}
    }
}

fn collect_locals_stmt(statements: &[Rc<Stmt>], locals: &mut Locals) {
    for statement in statements {
        match &*statement.stmtkind {
            StmtKind::Expr(expr) => {
                collect_locals_expr(expr, locals);
            }
            StmtKind::Let(_, pat, _) => {
                collect_locals_pat(pat.0.clone(), locals);
            }
            _ => {}
        }
    }
}

fn collect_locals_pat(pat: Rc<Pat>, locals: &mut Locals) {
    match &*pat.patkind {
        PatKind::Var(symbol) => {
            let len = locals.len();
            println!("adding {} to locals, pat_id = {}", symbol, pat.id);
            locals.entry(pat.id).or_insert(len as i32);
        }
        PatKind::Tuple(pats) => {
            for pat in pats {
                collect_locals_pat(pat.clone(), locals);
            }
        }
        PatKind::Variant(_, Some(inner)) => {
            collect_locals_pat(inner.clone(), locals);
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

fn idx_of_field(inf_ctx: &InferenceContext, accessed: Rc<Expr>, field: &str) -> u16 {
    let accessed_ty = inf_ctx.solution_of_node(accessed.id).unwrap();

    match accessed_ty {
        SolvedType::UdtInstance(symbol, _) => {
            let struct_ty = inf_ctx.struct_defs.get(&symbol).expect("not a struct type");
            let field_idx = struct_ty
                .fields
                .iter()
                .position(|f: &crate::statics::StructField| f.name == field)
                .unwrap();
            field_idx as u16
        }
        _ => panic!("not a udt"),
    }
}
