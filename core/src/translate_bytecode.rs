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
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

type OffsetTable = HashMap<NodeId, i32>;
type Lambdas = HashMap<NodeId, LambdaData>;

#[derive(Debug, Clone)]
struct LambdaData {
    label: Label,
    offset_table: OffsetTable,
    nlocals: usize,
    ncaptures: usize,
}

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
        let mut lambdas: Lambdas = HashMap::new();

        // Handle the main function (toplevels)
        {
            let mut locals = HashSet::new();
            for toplevel in self.toplevels.iter() {
                collect_locals_stmt(&toplevel.statements, &mut locals);
            }
            for i in 0..locals.len() {
                instructions.push(InstrOrLabel::Instr(Instr::PushNil));
            }
            let mut offset_table = OffsetTable::new();
            for (i, local) in locals.iter().enumerate() {
                offset_table.entry(*local).or_insert((i) as i32);
            }
            for toplevel in self.toplevels.iter() {
                for (i, statement) in toplevel.statements.iter().enumerate() {
                    self.translate_stmt(
                        statement.clone(),
                        i == toplevel.statements.len() - 1,
                        &offset_table,
                        &mut instructions,
                        &mut lambdas,
                    );
                }
            }
            instructions.push(InstrOrLabel::Instr(Instr::Stop));
        }

        // Handle function definitions
        for toplevel in self.toplevels.iter() {
            for statement in &toplevel.statements {
                if let StmtKind::FuncDef(name, args, _, body) = &*statement.stmtkind {
                    let func_name = name.patkind.get_identifier_of_variable();
                    let func_name_blacklist = [
                        "range", "fold", "sum", "sumf", "clamp", "concat", "map", "for_each",
                        "filter", "reverse", "print", "println",
                    ];
                    // don't generate code for functions in prelude, not ready for that yet.
                    if func_name_blacklist.contains(&func_name.as_str()) {
                        continue;
                    }
                    // println!("Generating code for function: {}", func_name);
                    instructions.push(InstrOrLabel::Label(func_name));
                    let mut locals = HashSet::new();
                    collect_locals_expr(body, &mut locals);
                    let locals_count = locals.len();
                    for _ in 0..locals_count {
                        instructions.push(InstrOrLabel::Instr(Instr::PushNil));
                    }
                    let mut offset_table = OffsetTable::new();
                    for (i, arg) in args.iter().rev().enumerate() {
                        offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
                    }
                    for (i, local) in locals.iter().enumerate() {
                        offset_table.entry(*local).or_insert((i) as i32);
                    }
                    let nargs = args.len();
                    self.translate_expr(
                        body.clone(),
                        &offset_table,
                        &mut instructions,
                        &mut lambdas,
                    );

                    if locals_count + nargs > 0 {
                        // pop all locals and arguments except one. The last one is the return value slot.
                        instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(-(nargs as i32))));
                        for _ in 0..(locals_count + nargs - 1) {
                            instructions.push(InstrOrLabel::Instr(Instr::Pop));
                        }
                    }

                    instructions.push(InstrOrLabel::Instr(Instr::Return));
                }
            }
        }

        // Handle lambdas
        for (node_id, data) in lambdas.clone() {
            let node = self.node_map.get(&node_id).unwrap();
            let expr = node.to_expr().unwrap();
            let ExprKind::Func(args, _, body) = &*expr.exprkind else {
                panic!()
            };

            instructions.push(InstrOrLabel::Label(data.label));

            self.translate_expr(
                body.clone(),
                &data.offset_table,
                &mut instructions,
                &mut lambdas,
            ); // TODO passing lambdas here is kind of weird and recursive. Should build list of lambdas in statics.rs instead.

            let nlocals = data.nlocals;
            let nargs = args.len();
            let ncaptures = data.ncaptures;
            if nlocals + nargs + ncaptures > 0 {
                // pop all locals and arguments except one. The last one is the return value slot.
                instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(-(nargs as i32))));
                for _ in 0..(nlocals + nargs + ncaptures - 1) {
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                }
            }

            instructions.push(InstrOrLabel::Instr(Instr::Return));
        }

        // Create functions for effects
        let effect_list = Effect::enumerate();
        for (i, effect) in effect_list.iter().enumerate() {
            instructions.push(InstrOrLabel::Label(effect.function_name()));
            instructions.push(InstrOrLabel::Instr(Instr::Effect(i as u16)));
            instructions.push(InstrOrLabel::Instr(Instr::Return));
        }

        for instr in &instructions {
            // println!("{}", instr);
        }
        let instructions = remove_labels(instructions, &self.inf_ctx.string_constants);
        let mut string_table: Vec<String> =
            vec!["".to_owned(); self.inf_ctx.string_constants.len()];
        for (s, idx) in self.inf_ctx.string_constants.iter() {
            string_table[*idx] = s.clone();
        }
        (instructions, string_table)
    }

    fn translate_expr(
        &self,
        expr: Rc<Expr>,
        offset_table: &OffsetTable,
        instructions: &mut Vec<InstrOrLabel>,
        lambdas: &mut Lambdas,
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
                                    instructions.push(InstrOrLabel::Instr(Instr::PushNil));
                                    instructions
                                        .push(InstrOrLabel::Instr(Instr::ConstructVariant { tag }));
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
                        let idx = offset_table.get(node_id).unwrap();
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
            ExprKind::Float(f) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushFloat(*f)));
            }
            ExprKind::Str(s) => {
                instructions.push(InstrOrLabel::Instr(Instr::PushString(s.clone())));
            }
            ExprKind::BinOp(left, op, right) => {
                self.translate_expr(left.clone(), offset_table, instructions, lambdas);
                self.translate_expr(right.clone(), offset_table, instructions, lambdas);
                match op {
                    BinOpcode::Add => instructions.push(InstrOrLabel::Instr(Instr::Add)),
                    BinOpcode::Subtract => instructions.push(InstrOrLabel::Instr(Instr::Subtract)),
                    BinOpcode::Multiply => instructions.push(InstrOrLabel::Instr(Instr::Multiply)),
                    BinOpcode::Divide => instructions.push(InstrOrLabel::Instr(Instr::Divide)),
                    BinOpcode::GreaterThan => {
                        instructions.push(InstrOrLabel::Instr(Instr::GreaterThan))
                    }
                    BinOpcode::LessThan => instructions.push(InstrOrLabel::Instr(Instr::LessThan)),
                    BinOpcode::GreaterThanOrEqual => {
                        instructions.push(InstrOrLabel::Instr(Instr::GreaterThanOrEqual))
                    }
                    BinOpcode::LessThanOrEqual => {
                        instructions.push(InstrOrLabel::Instr(Instr::LessThanOrEqual))
                    }
                    BinOpcode::Equals => instructions.push(InstrOrLabel::Instr(Instr::Equal)),
                    _ => panic!("op not implemented: {:?}", op),
                }
            }
            ExprKind::FuncAp(func, args) => {
                if let ExprKind::Var(symbol) = &*func.exprkind {
                    for arg in args {
                        self.translate_expr(arg.clone(), offset_table, instructions, lambdas);
                    }
                    let resolution = self.inf_ctx.name_resolutions.get(&func.id).unwrap();
                    match resolution {
                        Resolution::Node(node_id) => {
                            let node = self.node_map.get(node_id).unwrap();
                            dbg!(node);
                            let span = node.span();
                            let mut s = String::new();
                            span.display(&mut s, &self.sources, "function call");
                            println!("{}", s);
                            if let Some(stmt) = node.to_stmt() {
                                match &*stmt.stmtkind {
                                    StmtKind::FuncDef(name, _, _, _) => {
                                        instructions.push(InstrOrLabel::Instr(Instr::Call(
                                            name.patkind.get_identifier_of_variable(),
                                        )));
                                    }
                                    StmtKind::TypeDef(kind) => match &**kind {
                                        TypeDefKind::Struct(_, _, fields) => {
                                            instructions.push(InstrOrLabel::Instr(
                                                Instr::Construct(fields.len() as u16),
                                            ));
                                        }
                                        _ => unimplemented!(),
                                    },
                                    _ => panic!("unexpected stmt: {:?}", stmt.stmtkind),
                                }
                            } else {
                                // assume it's a function object
                                let idx = offset_table.get(node_id).unwrap();
                                instructions.push(InstrOrLabel::Instr(Instr::LoadOffset(*idx)));
                                instructions.push(InstrOrLabel::Instr(Instr::CallFuncObj));
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
                                        if args.len() > 1 {
                                            // turn the arguments (associated data) into a tuple
                                            instructions.push(InstrOrLabel::Instr(
                                                Instr::Construct(args.len() as u16),
                                            ));
                                        }
                                        instructions.push(InstrOrLabel::Instr(
                                            Instr::ConstructVariant { tag },
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
                                "sqrt_float" => {
                                    instructions.push(InstrOrLabel::Instr(Instr::SquareRoot));
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
                        offset_table,
                        instructions,
                        lambdas,
                    );
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), offset_table, instructions, lambdas);
                }
                instructions.push(InstrOrLabel::Instr(Instr::Construct(exprs.len() as u16)));
            }
            ExprKind::If(cond, then_block, Some(else_block)) => {
                self.translate_expr(cond.clone(), offset_table, instructions, lambdas);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                instructions.push(InstrOrLabel::Instr(Instr::JumpIf(then_label.clone())));
                self.translate_expr(else_block.clone(), offset_table, instructions, lambdas);
                instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                instructions.push(InstrOrLabel::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, instructions, lambdas);
                instructions.push(InstrOrLabel::Label(end_label));
            }
            ExprKind::If(cond, then_block, None) => {
                self.translate_expr(cond.clone(), offset_table, instructions, lambdas);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                instructions.push(InstrOrLabel::Instr(Instr::JumpIf(then_label.clone())));
                instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                instructions.push(InstrOrLabel::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, instructions, lambdas);
                instructions.push(InstrOrLabel::Label(end_label));
                instructions.push(InstrOrLabel::Instr(Instr::PushNil)); // TODO get rid of this
            }
            ExprKind::FieldAccess(accessed, field) => {
                // TODO, this downcast shouldn't be necessary
                let ExprKind::Var(field_name) = &*field.exprkind else {
                    panic!()
                };
                self.translate_expr(accessed.clone(), offset_table, instructions, lambdas);
                let idx = idx_of_field(&self.inf_ctx, accessed.clone(), field_name);
                instructions.push(InstrOrLabel::Instr(Instr::GetField(idx)));
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), offset_table, instructions, lambdas);
                }
                instructions.push(InstrOrLabel::Instr(Instr::Construct(exprs.len() as u16)));
            }
            ExprKind::IndexAccess(array, index) => {
                self.translate_expr(index.clone(), offset_table, instructions, lambdas);
                self.translate_expr(array.clone(), offset_table, instructions, lambdas);
                instructions.push(InstrOrLabel::Instr(Instr::GetIdx));
            }
            ExprKind::Match(expr, arms) => {
                let ty = self.inf_ctx.solution_of_node(expr.id).unwrap();

                self.translate_expr(expr.clone(), offset_table, instructions, lambdas);
                let end_label = make_label("endmatch");
                // Check scrutinee against each arm's pattern
                let arm_labels = arms
                    .iter()
                    .enumerate()
                    .map(|(i, _)| make_label(&format!("arm{}", i)))
                    .collect::<Vec<_>>();
                for (i, arm) in arms.iter().enumerate() {
                    let arm_label = arm_labels[i].clone();

                    // duplicate the scrutinee before doing a comparison
                    instructions.push(InstrOrLabel::Instr(Instr::Duplicate));
                    self.translate_pat_comparison(&ty, arm.pat.clone(), instructions);
                    instructions.push(InstrOrLabel::Instr(Instr::JumpIf(arm_label)));
                }
                for (i, arm) in arms.iter().enumerate() {
                    instructions.push(InstrOrLabel::Label(arm_labels[i].clone()));

                    self.handle_pat_binding(arm.pat.clone(), offset_table, instructions);

                    self.translate_expr(arm.expr.clone(), offset_table, instructions, lambdas);
                    if i != arms.len() - 1 {
                        instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                    }
                }
                instructions.push(InstrOrLabel::Label(end_label));
            }
            ExprKind::Func(args, _, body) => {
                let label = make_label("lambda");

                let mut locals = HashSet::new();
                collect_locals_expr(body, &mut locals);
                let locals_count = locals.len();
                let arg_set = args.iter().map(|(pat, _)| pat.id).collect::<HashSet<_>>();
                let mut captures = HashSet::new();
                self.collect_captures_expr(body, &locals, &arg_set, &mut captures);
                for capture in captures.iter() {
                    let node = self.node_map.get(&capture).unwrap();
                    let span = node.span();
                    let mut s = String::new();
                    span.display(&mut s, &self.sources, "capture");
                    println!("{}", s);
                }
                let ncaptures = captures.len();
                for i in 0..locals_count {
                    instructions.push(InstrOrLabel::Instr(Instr::PushNil));
                }

                let mut lambda_offset_table = OffsetTable::new();
                for (i, arg) in args.iter().rev().enumerate() {
                    lambda_offset_table
                        .entry(arg.0.id)
                        .or_insert(-(i as i32) - 1);
                }
                for (i, capture) in captures.iter().enumerate() {
                    lambda_offset_table.entry(*capture).or_insert(i as i32);
                }
                for (i, local) in locals.iter().enumerate() {
                    lambda_offset_table
                        .entry(*local)
                        .or_insert((i + captures.len()) as i32);
                }

                for capture in captures {
                    instructions.push(InstrOrLabel::Instr(Instr::LoadOffset(
                        *offset_table.get(&capture).unwrap(),
                    )));
                }

                lambdas.insert(
                    expr.id,
                    LambdaData {
                        label: label.clone(),
                        offset_table: lambda_offset_table,
                        nlocals: locals_count,
                        ncaptures,
                    },
                );

                instructions.push(InstrOrLabel::Instr(Instr::MakeClosure {
                    n_captured: ncaptures as u16,
                    func_addr: label,
                }));
            }
            _ => panic!("unimplemented: {:?}", expr.exprkind),
        }
    }

    // emit instructions for checking if a pattern matches the TOS, replacing it with a boolean
    fn translate_pat_comparison(
        &self,
        scrutinee_ty: &SolvedType,
        pat: Rc<Pat>,
        instructions: &mut Vec<InstrOrLabel>,
    ) {
        match &*pat.patkind {
            PatKind::Wildcard | PatKind::Var(_) | PatKind::Unit => {
                instructions.push(InstrOrLabel::Instr(Instr::Pop));
                instructions.push(InstrOrLabel::Instr(Instr::PushBool(true)));
                return;
            }
            _ => {}
        }

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
                PatKind::Variant(ctor, inner) => {
                    let adt = self.inf_ctx.adt_defs.get(symbol).unwrap();
                    let tag_fail_label = make_label("tag_fail");
                    let end_label = make_label("endvariant");

                    let tag = adt
                        .variants
                        .iter()
                        .position(|v| v.ctor == *ctor)
                        .expect("variant not found") as u16;

                    instructions.push(InstrOrLabel::Instr(Instr::Deconstruct));
                    instructions.push(InstrOrLabel::Instr(Instr::PushInt(tag as AbraInt)));
                    instructions.push(InstrOrLabel::Instr(Instr::Equal));
                    instructions.push(InstrOrLabel::Instr(Instr::Not));
                    instructions.push(InstrOrLabel::Instr(Instr::JumpIf(tag_fail_label.clone())));

                    if let Some(inner) = inner {
                        let inner_ty = self.inf_ctx.solution_of_node(inner.id).unwrap();
                        self.translate_pat_comparison(&inner_ty, inner.clone(), instructions);
                        instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                    } else {
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                        instructions.push(InstrOrLabel::Instr(Instr::PushBool(true)));
                        instructions.push(InstrOrLabel::Instr(Instr::Jump(end_label.clone())));
                    }

                    // FAILURE
                    instructions.push(InstrOrLabel::Label(tag_fail_label));
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));

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
                    instructions.push(InstrOrLabel::Label(failure_labels[0].clone()));
                    for label in &failure_labels[1..] {
                        instructions.push(InstrOrLabel::Instr(Instr::Pop));
                        instructions.push(InstrOrLabel::Label(label.clone()));
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
        locals: &OffsetTable,
        instructions: &mut Vec<InstrOrLabel>,
        lambdas: &mut Lambdas,
    ) {
        match &*stmt.stmtkind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr.clone(), locals, instructions, lambdas);
                self.handle_pat_binding(pat.0.clone(), locals, instructions);
            }
            StmtKind::Set(expr1, rvalue) => match &*expr1.exprkind {
                ExprKind::Var(_) => {
                    let Resolution::Node(node_id) =
                        self.inf_ctx.name_resolutions.get(&expr1.id).unwrap()
                    else {
                        panic!("expected variableto be defined in node");
                    };
                    let idx = locals.get(node_id).unwrap();
                    self.translate_expr(rvalue.clone(), locals, instructions, lambdas);
                    instructions.push(InstrOrLabel::Instr(Instr::StoreOffset(*idx)));
                }
                ExprKind::FieldAccess(accessed, field) => {
                    // TODO, this downcast shouldn't be necessary
                    let ExprKind::Var(field_name) = &*field.exprkind else {
                        panic!()
                    };
                    self.translate_expr(rvalue.clone(), locals, instructions, lambdas);
                    self.translate_expr(accessed.clone(), locals, instructions, lambdas);
                    let idx = idx_of_field(&self.inf_ctx, accessed.clone(), field_name);
                    instructions.push(InstrOrLabel::Instr(Instr::SetField(idx)));
                }
                ExprKind::IndexAccess(array, index) => {
                    self.translate_expr(rvalue.clone(), locals, instructions, lambdas);
                    self.translate_expr(index.clone(), locals, instructions, lambdas);
                    self.translate_expr(array.clone(), locals, instructions, lambdas);
                    instructions.push(InstrOrLabel::Instr(Instr::SetIdx));
                }
                _ => unimplemented!(),
            },
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), locals, instructions, lambdas);
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

    fn handle_pat_binding(
        &self,
        pat: Rc<Pat>,
        locals: &OffsetTable,
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
                    self.handle_pat_binding(pat.clone(), locals, instructions);
                }
            }
            PatKind::Variant(_, inner) => {
                if let Some(inner) = inner {
                    // unpack tag and associated data
                    instructions.push(InstrOrLabel::Instr(Instr::Deconstruct));
                    // pop tag
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                    self.handle_pat_binding(inner.clone(), locals, instructions);
                } else {
                    instructions.push(InstrOrLabel::Instr(Instr::Pop));
                }
            }
            PatKind::Unit
            | PatKind::Bool(..)
            | PatKind::Int(..)
            | PatKind::Float(..)
            | PatKind::Str(..)
            | PatKind::Wildcard => {
                instructions.push(InstrOrLabel::Instr(Instr::Pop));
            }
        }
    }

    fn collect_captures_expr(
        &self,
        expr: &Expr,
        locals: &HashSet<NodeId>,
        arg_set: &HashSet<NodeId>,
        captures: &mut HashSet<NodeId>,
    ) {
        match &*expr.exprkind {
            ExprKind::Unit
            | ExprKind::Bool(_)
            | ExprKind::Int(_)
            | ExprKind::Float(_)
            | ExprKind::Str(_) => {}
            ExprKind::Var(_) => {
                let resolution = self.inf_ctx.name_resolutions.get(&expr.id).unwrap();
                if let Resolution::Node(node_id) = resolution {
                    if !locals.contains(node_id) && !arg_set.contains(node_id) {
                        captures.insert(*node_id);
                    }
                }
            }

            ExprKind::Block(statements) => {
                for statement in statements {
                    self.collect_captures_stmt(&[statement.clone()], locals, arg_set, captures);
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    self.collect_captures_expr(&arm.expr, locals, arg_set, captures);
                }
            }
            ExprKind::Func(_, _, body) => {
                self.collect_captures_expr(body, locals, arg_set, captures);
            }
            ExprKind::List(exprs) => {
                for expr in exprs {
                    self.collect_captures_expr(expr, locals, arg_set, captures);
                }
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.collect_captures_expr(expr, locals, arg_set, captures);
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.collect_captures_expr(expr, locals, arg_set, captures);
                }
            }
            ExprKind::BinOp(left, _, right) => {
                self.collect_captures_expr(left, locals, arg_set, captures);
                self.collect_captures_expr(right, locals, arg_set, captures);
            }
            ExprKind::FieldAccess(accessed, _) => {
                self.collect_captures_expr(accessed, locals, arg_set, captures);
            }
            ExprKind::IndexAccess(array, index) => {
                self.collect_captures_expr(array, locals, arg_set, captures);
                self.collect_captures_expr(index, locals, arg_set, captures);
            }
            ExprKind::FuncAp(func, args) => {
                self.collect_captures_expr(func, locals, arg_set, captures);
                for arg in args {
                    self.collect_captures_expr(arg, locals, arg_set, captures);
                }
            }
            ExprKind::If(cond, then_block, else_block) => {
                self.collect_captures_expr(cond, locals, arg_set, captures);
                self.collect_captures_expr(then_block, locals, arg_set, captures);
                if let Some(else_block) = else_block {
                    self.collect_captures_expr(else_block, locals, arg_set, captures);
                }
            }
            ExprKind::WhileLoop(cond, body) => {
                self.collect_captures_expr(cond, locals, arg_set, captures);
                self.collect_captures_expr(body, locals, arg_set, captures);
            }
        }
    }

    fn collect_captures_stmt(
        &self,
        statements: &[Rc<Stmt>],
        locals: &HashSet<NodeId>,
        arg_set: &HashSet<NodeId>,
        captures: &mut HashSet<NodeId>,
    ) {
        for statement in statements {
            match &*statement.stmtkind {
                StmtKind::Expr(expr) => {
                    self.collect_captures_expr(expr, locals, arg_set, captures);
                }
                StmtKind::Let(_, _, expr) => {
                    self.collect_captures_expr(expr, locals, arg_set, captures);
                }
                StmtKind::Set(_, expr) => {
                    self.collect_captures_expr(expr, locals, arg_set, captures);
                }
                StmtKind::FuncDef(..) => {}
                StmtKind::InterfaceImpl(..) => {}
                StmtKind::InterfaceDef(..) => {}
                StmtKind::TypeDef(..) => {}
            }
        }
    }
}

fn collect_locals_expr(expr: &Expr, locals: &mut HashSet<NodeId>) {
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

fn collect_locals_stmt(statements: &[Rc<Stmt>], locals: &mut HashSet<NodeId>) {
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

fn collect_locals_pat(pat: Rc<Pat>, locals: &mut HashSet<NodeId>) {
    match &*pat.patkind {
        PatKind::Var(symbol) => {
            let len = locals.len();
            println!("adding {} to locals, pat_id = {}", symbol, pat.id);
            locals.insert(pat.id);
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
