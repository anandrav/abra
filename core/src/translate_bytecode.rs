use crate::assembly::{remove_labels, Instr, Item, Label};
use crate::ast::BinOpcode;
use crate::ast::{Node, NodeId, Sources, Symbol, Toplevel};
use crate::builtin::Builtin;
use crate::effects::EffectStruct;
use crate::environment::Environment;
use crate::statics::{ty_fits_impl_ty, Monotype, Prov, Resolution, SolvedType};
use crate::vm::{AbraInt, Instr as VmInstr};
use crate::{
    ast::{Expr, ExprKind, NodeMap, Pat, PatKind, Stmt, StmtKind},
    statics::StaticsContext,
};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::mem;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

type OffsetTable = HashMap<NodeId, i32>;
type Lambdas = HashMap<NodeId, LambdaData>;
type OverloadedFuncLabels = BTreeMap<OverloadedFuncDesc, Label>;
type MonomorphEnv = Environment<Symbol, SolvedType>;
pub(crate) type LabelMap = HashMap<Label, usize>;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq)]
struct OverloadedFuncDesc {
    name: Symbol,
    impl_type: Monotype,
    definition_node: NodeId,
}

#[derive(Debug, Clone)]
struct LambdaData {
    label: Label,
    offset_table: OffsetTable,
    nlocals: usize,
    ncaptures: usize,
}

#[derive(Debug)]
pub(crate) struct Translator {
    statics: StaticsContext,
    node_map: NodeMap,
    sources: Sources,
    toplevels: Vec<Rc<Toplevel>>,
    effects: Vec<EffectStruct>,
}

#[derive(Debug, Default)]
struct TranslatorState {
    items: Vec<Item>,
    lambdas: Lambdas,
    overloaded_func_map: OverloadedFuncLabels,
    overloaded_methods_to_generate: Vec<(OverloadedFuncDesc, SolvedType)>,
}

fn emit(st: &mut TranslatorState, i: impl Into<Item>) {
    st.items.push(i.into());
}

#[derive(Debug)]
pub struct CompiledProgram {
    pub(crate) instructions: Vec<VmInstr>,
    pub(crate) label_map: LabelMap,
    pub(crate) string_table: Vec<String>,
}

impl Translator {
    pub(crate) fn new(
        statics: StaticsContext,
        node_map: NodeMap,
        sources: Sources,
        toplevels: Vec<Rc<Toplevel>>,
        effects: Vec<EffectStruct>,
    ) -> Self {
        Self {
            statics,
            node_map,
            sources,
            toplevels,
            effects,
        }
    }

    pub(crate) fn translate(&self) -> CompiledProgram {
        let mut translator_state = TranslatorState::default();
        let st = &mut translator_state;

        let monomorph_env = MonomorphEnv::empty();

        // Handle the main function (toplevels)
        {
            let mut locals = HashSet::new();
            for toplevel in self.toplevels.iter() {
                collect_locals_stmt(&toplevel.statements, &mut locals);
            }
            for _ in 0..locals.len() {
                emit(st, Instr::PushNil);
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
                        monomorph_env.clone(),
                        st,
                    );
                }
            }
            emit(st, Instr::Return);
        }

        // Handle ordinary function (not overloaded, not a closure) definitions
        for toplevel in self.toplevels.iter() {
            for stmt in &toplevel.statements {
                self.translate_stmt_static(stmt.clone(), st, false);
            }
        }

        // Handle lambdas with captures
        for (node_id, data) in st.lambdas.clone() {
            let node = self.node_map.get(&node_id).unwrap();
            let expr = node.to_expr().unwrap();
            let ExprKind::Func(args, _, body) = &*expr.exprkind else {
                panic!()
            };

            emit(st, Item::Label(data.label));

            self.translate_expr(body.clone(), &data.offset_table, monomorph_env.clone(), st); // TODO passing lambdas here is kind of weird and recursive. Should build list of lambdas in statics.rs instead.

            let nlocals = data.nlocals;
            let nargs = args.len();
            let ncaptures = data.ncaptures;
            if nlocals + nargs + ncaptures > 0 {
                // pop all locals and arguments except one. The last one is the return value slot.
                emit(st, Instr::StoreOffset(-(nargs as i32)));
                for _ in 0..(nlocals + nargs + ncaptures - 1) {
                    emit(st, Instr::Pop);
                }
            }

            emit(st, Instr::Return);
        }

        // Handle interface method implementations
        while !st.overloaded_methods_to_generate.is_empty() {
            let mut iteration = Vec::new();
            mem::swap(&mut (iteration), &mut st.overloaded_methods_to_generate);
            for (desc, substituted_ty) in iteration {
                let definition_id = desc.definition_node;

                let StmtKind::FuncDef(pat, args, _, body) = &*self
                    .node_map
                    .get(&definition_id)
                    .unwrap()
                    .to_stmt()
                    .unwrap()
                    .stmtkind
                else {
                    panic!()
                };

                let overloaded_func_ty = self.statics.solution_of_node(pat.id()).unwrap();
                let monomorph_env = MonomorphEnv::empty();
                update_monomorph_env(monomorph_env.clone(), overloaded_func_ty, substituted_ty);

                let label = st.overloaded_func_map.get(&desc).unwrap();
                emit(st, Item::Label(label.clone()));

                let mut locals = HashSet::new();
                collect_locals_expr(body, &mut locals);
                let locals_count = locals.len();
                for _ in 0..locals_count {
                    emit(st, Instr::PushNil);
                }
                let mut offset_table = OffsetTable::new();
                for (i, arg) in args.iter().rev().enumerate() {
                    offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
                }
                for (i, local) in locals.iter().enumerate() {
                    offset_table.entry(*local).or_insert((i) as i32);
                }
                let nargs = args.len();
                self.translate_expr(body.clone(), &offset_table, monomorph_env.clone(), st);

                if locals_count + nargs > 0 {
                    // pop all locals and arguments except one. The last one is the return value slot.
                    emit(st, Instr::StoreOffset(-(nargs as i32)));
                    for _ in 0..(locals_count + nargs - 1) {
                        emit(st, Instr::Pop);
                    }
                }

                emit(st, Instr::Return);
            }
        }

        // Create functions for effects
        for (i, effect) in self.effects.iter().enumerate() {
            emit(st, Item::Label(effect.name.clone()));
            emit(st, Instr::Effect(i as u16));
            emit(st, Instr::Return);
        }

        for _item in st.items.iter() {
            // println!("{}", _item);
        }

        let (instructions, label_map) = remove_labels(&st.items, &self.statics.string_constants);
        let mut string_table: Vec<String> =
            vec!["".to_owned(); self.statics.string_constants.len()];
        for (s, idx) in self.statics.string_constants.iter() {
            string_table[*idx] = s.clone();
        }
        CompiledProgram {
            instructions,
            label_map,
            string_table,
        }
    }

    fn translate_expr(
        &self,
        expr: Rc<Expr>,
        offset_table: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        // println!("translating expr: {:?}", expr.exprkind);
        match &*expr.exprkind {
            ExprKind::Var(symbol) => {
                // adt variant
                match self.statics.name_resolutions.get(&expr.id).unwrap() {
                    Resolution::Variant(tag, _) => {
                        emit(st, Instr::PushNil);
                        emit(st, Instr::ConstructVariant { tag: *tag });
                    }
                    Resolution::Var(node_id) => {
                        let span = self.node_map.get(node_id).unwrap().span();
                        let mut s = String::new();
                        span.display(
                            &mut s,
                            &self.sources,
                            &format!("symbol {} resolved to", symbol),
                        );
                        // println!("{}", s);
                        let idx = offset_table.get(node_id).unwrap();
                        emit(st, Instr::LoadOffset(*idx));
                    }
                    Resolution::Builtin(b) => {
                        match b {
                            Builtin::Newline => {
                                emit(st, Instr::PushString("\n".to_owned()));
                            }
                            _ => {
                                // TODO: generate functions for builtins
                                unimplemented!()
                            }
                        }
                    }
                    Resolution::Effect(_) => {
                        // TODO: generate functions for effects
                        unimplemented!()
                    }
                    Resolution::StructDefinition(_) => {
                        // TODO: generate functions for structs
                        unimplemented!()
                    }
                    Resolution::FunctionDefinition(_, name) => {
                        emit(
                            st,
                            Instr::MakeClosure {
                                n_captured: 0,
                                func_addr: name.clone(),
                            },
                        );
                    }
                    Resolution::InterfaceMethod { .. } => {
                        unimplemented!()
                    }
                }
            }
            ExprKind::Unit => {
                emit(st, Instr::PushNil);
            }
            ExprKind::Bool(b) => {
                emit(st, Instr::PushBool(*b));
            }
            ExprKind::Int(i) => {
                emit(st, Instr::PushInt(*i));
            }
            ExprKind::Float(f) => {
                emit(st, Instr::PushFloat(*f));
            }
            ExprKind::Str(s) => {
                emit(st, Instr::PushString(s.clone()));
            }
            ExprKind::BinOp(left, op, right) => {
                self.translate_expr(left.clone(), offset_table, monomorph_env.clone(), st);
                self.translate_expr(right.clone(), offset_table, monomorph_env.clone(), st);
                match op {
                    BinOpcode::Add => emit(st, Instr::Add),
                    BinOpcode::Subtract => emit(st, Instr::Subtract),
                    BinOpcode::Multiply => emit(st, Instr::Multiply),
                    BinOpcode::Divide => emit(st, Instr::Divide),
                    BinOpcode::GreaterThan => emit(st, Instr::GreaterThan),
                    BinOpcode::LessThan => emit(st, Instr::LessThan),
                    BinOpcode::GreaterThanOrEqual => emit(st, Instr::GreaterThanOrEqual),
                    BinOpcode::LessThanOrEqual => emit(st, Instr::LessThanOrEqual),
                    BinOpcode::Equal => emit(st, Instr::Equal),
                    BinOpcode::Concat => emit(st, Instr::ConcatStrings),
                    BinOpcode::Or => emit(st, Instr::Or),
                    BinOpcode::And => emit(st, Instr::And),
                    BinOpcode::Pow => emit(st, Instr::Power),
                    BinOpcode::Mod => emit(st, Instr::Modulo),
                }
            }
            ExprKind::FuncAp(func, args) => {
                if let ExprKind::Var(_) = &*func.exprkind {
                    for arg in args {
                        self.translate_expr(arg.clone(), offset_table, monomorph_env.clone(), st);
                    }
                    let node = self.node_map.get(&func.id).unwrap();
                    let span = node.span();
                    let mut s = String::new();
                    span.display(&mut s, &self.sources, "function ap");
                    // println!("{}", s);
                    let resolution = self.statics.name_resolutions.get(&func.id).unwrap();
                    match resolution {
                        Resolution::Var(node_id) => {
                            // assume it's a function object
                            let idx = offset_table.get(node_id).unwrap();
                            emit(st, Instr::LoadOffset(*idx));
                            emit(st, Instr::CallFuncObj);
                        }
                        Resolution::FunctionDefinition(node_id, name) => {
                            // println!("emitting Call of function: {}", name);
                            let StmtKind::FuncDef(pat, _, _, _) = &*self
                                .node_map
                                .get(node_id)
                                .unwrap()
                                .to_stmt()
                                .unwrap()
                                .stmtkind
                            else {
                                panic!()
                            };

                            let func_name = &pat.patkind.get_identifier_of_variable();
                            let func_ty = self.statics.solution_of_node(pat.id).unwrap();
                            if !func_ty.is_overloaded() {
                                emit(st, Instr::Call(name.clone()));
                            } else {
                                let node = self.node_map.get(&func.id).unwrap();
                                let span = node.span();
                                let mut s = String::new();
                                span.display(&mut s, &self.sources, " method ap");
                                // println!("{}", s);

                                let specific_func_ty =
                                    self.statics.solution_of_node(func.id).unwrap();

                                let substituted_ty =
                                    subst_with_monomorphic_env(monomorph_env, specific_func_ty);
                                // println!("substituted type: {:?}", substituted_ty);

                                self.handle_overloaded_func(
                                    st,
                                    substituted_ty,
                                    func_name,
                                    *node_id,
                                );
                            }
                        }
                        Resolution::InterfaceMethod(name) => {
                            let node = self.node_map.get(&func.id).unwrap();
                            let span = node.span();
                            let mut s = String::new();
                            span.display(&mut s, &self.sources, " method ap");
                            // println!("{}", s);

                            let func_ty = self.statics.solution_of_node(func.id).unwrap();
                            let substituted_ty =
                                subst_with_monomorphic_env(monomorph_env.clone(), func_ty);
                            // println!("substituted type: {:?}", substituted_ty);
                            let def_id =
                                self.get_func_definition_node(name, substituted_ty.clone());
                            self.handle_overloaded_func(st, substituted_ty, name, def_id);
                        }
                        Resolution::StructDefinition(nargs) => {
                            emit(st, Instr::Construct(*nargs));
                        }
                        Resolution::Variant(tag, nargs) => {
                            if *nargs > 1 {
                                // turn the arguments (associated data) into a tuple
                                emit(st, Instr::Construct(*nargs));
                            }
                            emit(st, Instr::ConstructVariant { tag: *tag });
                        }
                        Resolution::Builtin(b) => match b {
                            Builtin::AddInt => {
                                emit(st, Instr::Add);
                            }
                            Builtin::SubtractInt => {
                                emit(st, Instr::Subtract);
                            }
                            Builtin::MultiplyInt => {
                                emit(st, Instr::Multiply);
                            }
                            Builtin::DivideInt => {
                                emit(st, Instr::Divide);
                            }
                            Builtin::PowerInt => {
                                emit(st, Instr::Power);
                            }
                            Builtin::ModuloInt => {
                                emit(st, Instr::Modulo);
                            }
                            Builtin::SqrtInt => {
                                emit(st, Instr::SquareRoot);
                            }
                            Builtin::AddFloat => {
                                emit(st, Instr::Add);
                            }
                            Builtin::SubtractFloat => {
                                emit(st, Instr::Subtract);
                            }
                            Builtin::MultiplyFloat => {
                                emit(st, Instr::Multiply);
                            }
                            Builtin::DivideFloat => {
                                emit(st, Instr::Divide);
                            }
                            Builtin::ModuloFloat => {
                                emit(st, Instr::Modulo);
                            }
                            Builtin::PowerFloat => {
                                emit(st, Instr::Power);
                            }
                            Builtin::SqrtFloat => {
                                emit(st, Instr::SquareRoot);
                            }
                            Builtin::LessThanInt => {
                                emit(st, Instr::LessThan);
                            }
                            Builtin::LessThanOrEqualInt => {
                                emit(st, Instr::LessThanOrEqual);
                            }
                            Builtin::GreaterThanInt => {
                                emit(st, Instr::GreaterThan);
                            }
                            Builtin::GreaterThanOrEqualInt => {
                                emit(st, Instr::GreaterThanOrEqual);
                            }
                            Builtin::EqualInt => {
                                emit(st, Instr::Equal);
                            }
                            Builtin::LessThanFloat => {
                                emit(st, Instr::LessThan);
                            }
                            Builtin::LessThanOrEqualFloat => {
                                emit(st, Instr::LessThanOrEqual);
                            }
                            Builtin::GreaterThanFloat => {
                                emit(st, Instr::GreaterThan);
                            }
                            Builtin::GreaterThanOrEqualFloat => {
                                emit(st, Instr::GreaterThanOrEqual);
                            }
                            Builtin::EqualFloat => {
                                emit(st, Instr::Equal);
                            }
                            Builtin::EqualString => {
                                emit(st, Instr::Equal);
                            }
                            Builtin::IntToString => {
                                emit(st, Instr::IntToString);
                            }
                            Builtin::FloatToString => {
                                emit(st, Instr::FloatToString);
                            }
                            Builtin::ArrayAppend => {
                                emit(st, Instr::ArrayAppend);
                            }
                            Builtin::ArrayLength => {
                                emit(st, Instr::ArrayLength);
                            }
                            Builtin::ArrayPop => {
                                emit(st, Instr::ArrayPop);
                            }
                            Builtin::Newline => {
                                panic!("not a function");
                            }
                        },
                        Resolution::Effect(e) => {
                            emit(st, Instr::Effect(*e));
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
                        monomorph_env.clone(),
                        st,
                    );
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                }
                emit(st, Instr::Construct(exprs.len() as u16));
            }
            ExprKind::If(cond, then_block, Some(else_block)) => {
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                emit(st, Instr::JumpIf(then_label.clone()));
                self.translate_expr(else_block.clone(), offset_table, monomorph_env.clone(), st);
                emit(st, Instr::Jump(end_label.clone()));
                emit(st, Item::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, monomorph_env.clone(), st);
                emit(st, Item::Label(end_label));
            }
            ExprKind::If(cond, then_block, None) => {
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                emit(st, Instr::JumpIf(then_label.clone()));
                emit(st, Instr::Jump(end_label.clone()));
                emit(st, Item::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, monomorph_env.clone(), st);
                emit(st, Item::Label(end_label));
                emit(st, Instr::PushNil); // TODO get rid of this unnecessary overhead
            }
            ExprKind::FieldAccess(accessed, field) => {
                // TODO, this downcast shouldn't be necessary
                let ExprKind::Var(field_name) = &*field.exprkind else {
                    panic!()
                };
                self.translate_expr(accessed.clone(), offset_table, monomorph_env.clone(), st);
                let idx = idx_of_field(&self.statics, accessed.clone(), field_name);
                emit(st, Instr::GetField(idx));
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                }
                emit(st, Instr::Construct(exprs.len() as u16));
            }
            ExprKind::List(exprs) => {
                fn translate_list(
                    translator: &Translator,
                    exprs: &[Rc<Expr>],
                    offset_table: &OffsetTable,
                    monomorph_env: MonomorphEnv,
                    st: &mut TranslatorState,
                ) {
                    if exprs.is_empty() {
                        emit(st, Instr::PushNil);
                        emit(st, Instr::ConstructVariant { tag: 0 });
                    } else {
                        translator.translate_expr(
                            exprs[0].clone(),
                            offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                        translate_list(
                            translator,
                            &exprs[1..],
                            offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                        emit(st, Instr::Construct(2)); // (head, tail)
                        emit(st, Instr::ConstructVariant { tag: 1 });
                    }
                }

                translate_list(self, exprs, offset_table, monomorph_env.clone(), st);
            }
            ExprKind::IndexAccess(array, index) => {
                self.translate_expr(index.clone(), offset_table, monomorph_env.clone(), st);
                self.translate_expr(array.clone(), offset_table, monomorph_env.clone(), st);
                emit(st, Instr::GetIdx);
            }
            ExprKind::Match(expr, arms) => {
                let ty = self.statics.solution_of_node(expr.id).unwrap();

                self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
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
                    emit(st, Instr::Duplicate);
                    self.translate_pat_comparison(&ty, arm.pat.clone(), st);
                    emit(st, Instr::JumpIf(arm_label));
                }
                for (i, arm) in arms.iter().enumerate() {
                    emit(st, Item::Label(arm_labels[i].clone()));

                    self.handle_pat_binding(arm.pat.clone(), offset_table, st);

                    self.translate_expr(arm.expr.clone(), offset_table, monomorph_env.clone(), st);
                    if i != arms.len() - 1 {
                        emit(st, Instr::Jump(end_label.clone()));
                    }
                }
                emit(st, Item::Label(end_label));
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
                    let node = self.node_map.get(capture).unwrap();
                    let span = node.span();
                    let mut s = String::new();
                    span.display(&mut s, &self.sources, "capture");
                    // println!("{}", s);
                }
                let ncaptures = captures.len();
                for _ in 0..locals_count {
                    emit(st, Instr::PushNil);
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
                    emit(st, Instr::LoadOffset(*offset_table.get(&capture).unwrap()));
                }

                st.lambdas.insert(
                    expr.id,
                    LambdaData {
                        label: label.clone(),
                        offset_table: lambda_offset_table,
                        nlocals: locals_count,
                        ncaptures,
                    },
                );

                emit(
                    st,
                    Instr::MakeClosure {
                        n_captured: ncaptures as u16,
                        func_addr: label,
                    },
                );
            }
            ExprKind::WhileLoop(cond, body) => {
                let start_label = make_label("while_start");
                let end_label = make_label("while_end");

                emit(st, Item::Label(start_label.clone()));
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                emit(st, Instr::Not);
                emit(st, Instr::JumpIf(end_label.clone()));
                self.translate_expr(body.clone(), offset_table, monomorph_env.clone(), st);
                emit(st, Instr::Jump(start_label));
                emit(st, Item::Label(end_label));
                emit(st, Instr::PushNil);
            }
        }
    }

    // emit items for checking if a pattern matches the TOS, replacing it with a boolean
    fn translate_pat_comparison(
        &self,
        scrutinee_ty: &SolvedType,
        pat: Rc<Pat>,
        st: &mut TranslatorState,
    ) {
        match &*pat.patkind {
            PatKind::Wildcard | PatKind::Var(_) | PatKind::Unit => {
                emit(st, Instr::Pop);
                emit(st, Instr::PushBool(true));
                return;
            }
            _ => {}
        }

        match scrutinee_ty {
            SolvedType::Int => match &*pat.patkind {
                PatKind::Int(i) => {
                    emit(st, Instr::PushInt(*i));
                    emit(st, Instr::Equal);
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            SolvedType::Bool => match &*pat.patkind {
                PatKind::Bool(b) => {
                    emit(st, Instr::PushBool(*b));
                    emit(st, Instr::Equal);
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            SolvedType::UdtInstance(symbol, _) => match &*pat.patkind {
                PatKind::Variant(ctor, inner) => {
                    let adt = self.statics.adt_defs.get(symbol).unwrap();
                    let tag_fail_label = make_label("tag_fail");
                    let end_label = make_label("endvariant");

                    let tag = adt
                        .variants
                        .iter()
                        .position(|v| v.ctor == *ctor)
                        .expect("variant not found") as u16;

                    emit(st, Instr::Deconstruct);
                    emit(st, Instr::PushInt(tag as AbraInt));
                    emit(st, Instr::Equal);
                    emit(st, Instr::Not);
                    emit(st, Instr::JumpIf(tag_fail_label.clone()));

                    if let Some(inner) = inner {
                        let inner_ty = self.statics.solution_of_node(inner.id).unwrap();
                        self.translate_pat_comparison(&inner_ty, inner.clone(), st);
                        emit(st, Instr::Jump(end_label.clone()));
                    } else {
                        emit(st, Instr::Pop);
                        emit(st, Instr::PushBool(true));
                        emit(st, Instr::Jump(end_label.clone()));
                    }

                    // FAILURE
                    emit(st, Item::Label(tag_fail_label));
                    emit(st, Instr::Pop);

                    emit(st, Instr::PushBool(false));

                    emit(st, Item::Label(end_label));
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            SolvedType::Tuple(types) => match &*pat.patkind {
                PatKind::Tuple(pats) => {
                    let final_element_success_label = make_label("tuple_success");
                    let end_label = make_label("endtuple");
                    // spill tuple elements onto stack
                    emit(st, Instr::Deconstruct);
                    // for each element of tuple pattern, compare to TOS
                    // if the comparison fails, pop all remaining tuple elements and jump to the next arm
                    // if it makes it through each tuple element, jump to the arm's expression
                    let failure_labels = (0..pats.len())
                        .map(|_| make_label("tuple_fail"))
                        .collect::<Vec<_>>();
                    for (i, pat) in pats.iter().enumerate() {
                        let ty = &types[i];
                        self.translate_pat_comparison(ty, pat.clone(), st);
                        let is_last = i == pats.len() - 1;
                        emit(st, Instr::Not);
                        emit(st, Instr::JumpIf(failure_labels[i].clone()));
                        // SUCCESS
                        if is_last {
                            emit(st, Instr::Jump(final_element_success_label.clone()));
                        }
                    }
                    // SUCCESS CASE
                    emit(st, Item::Label(final_element_success_label));
                    emit(st, Instr::PushBool(true));
                    emit(st, Instr::Jump(end_label.clone()));

                    // FAILURE CASE
                    // clean up the remaining tuple elements before yielding false
                    emit(st, Item::Label(failure_labels[0].clone()));
                    for label in &failure_labels[1..] {
                        emit(st, Instr::Pop);
                        emit(st, Item::Label(label.clone()));
                    }
                    emit(st, Instr::PushBool(false));

                    emit(st, Item::Label(end_label));
                }
                _ => panic!("unexpected pattern: {:?}", pat.patkind),
            },
            _ => unimplemented!(),
        }
    }

    fn translate_stmt_static(&self, stmt: Rc<Stmt>, st: &mut TranslatorState, iface_method: bool) {
        match &*stmt.stmtkind {
            StmtKind::Let(..) => {}
            StmtKind::Set(..) => {}
            StmtKind::Expr(..) => {}
            StmtKind::InterfaceImpl(_, _, stmts) => {
                for stmt in stmts {
                    self.translate_stmt_static(stmt.clone(), st, true);
                }
            }
            StmtKind::FuncDef(name, args, _, body) => {
                // TODO last here
                // TODO: check if overloaded. If so, handle differently.
                // (this could be an overloaded function or an interface method)
                let func_ty = self.statics.solution_of_node(name.id).unwrap();
                let func_name = name.patkind.get_identifier_of_variable();

                if func_ty.is_overloaded() // println: 'a ToString -> ()
                || iface_method
                // to_string: 'a ToString -> String
                {
                    return;
                }

                // println!("Generating code for function: {}", func_name);
                emit(st, Item::Label(func_name));
                let mut locals = HashSet::new();
                collect_locals_expr(body, &mut locals);
                let locals_count = locals.len();
                for _ in 0..locals_count {
                    emit(st, Instr::PushNil);
                }
                let mut offset_table = OffsetTable::new();
                for (i, arg) in args.iter().rev().enumerate() {
                    offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
                }
                for (i, local) in locals.iter().enumerate() {
                    offset_table.entry(*local).or_insert((i) as i32);
                }
                let nargs = args.len();
                self.translate_expr(body.clone(), &offset_table, MonomorphEnv::empty(), st);

                if locals_count + nargs > 0 {
                    // pop all locals and arguments except one. The last one is the return value slot.
                    emit(st, Instr::StoreOffset(-(nargs as i32)));
                    for _ in 0..(locals_count + nargs - 1) {
                        emit(st, Instr::Pop);
                    }
                }

                emit(st, Instr::Return);
            }
            StmtKind::InterfaceDef(..) | StmtKind::TypeDef(..) => {
                // noop
            }
        }
    }

    fn translate_stmt(
        &self,
        stmt: Rc<Stmt>,
        is_last: bool,
        locals: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        match &*stmt.stmtkind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr.clone(), locals, monomorph_env.clone(), st);
                self.handle_pat_binding(pat.0.clone(), locals, st);
            }
            StmtKind::Set(expr1, rvalue) => match &*expr1.exprkind {
                ExprKind::Var(_) => {
                    let Resolution::Var(node_id) =
                        self.statics.name_resolutions.get(&expr1.id).unwrap()
                    else {
                        panic!("expected variableto be defined in node");
                    };
                    let idx = locals.get(node_id).unwrap();
                    self.translate_expr(rvalue.clone(), locals, monomorph_env.clone(), st);
                    emit(st, Instr::StoreOffset(*idx));
                }
                ExprKind::FieldAccess(accessed, field) => {
                    // TODO, this downcast shouldn't be necessary
                    let ExprKind::Var(field_name) = &*field.exprkind else {
                        panic!()
                    };
                    self.translate_expr(rvalue.clone(), locals, monomorph_env.clone(), st);
                    self.translate_expr(accessed.clone(), locals, monomorph_env.clone(), st);
                    let idx = idx_of_field(&self.statics, accessed.clone(), field_name);
                    emit(st, Instr::SetField(idx));
                }
                ExprKind::IndexAccess(array, index) => {
                    self.translate_expr(rvalue.clone(), locals, monomorph_env.clone(), st);
                    self.translate_expr(index.clone(), locals, monomorph_env.clone(), st);
                    self.translate_expr(array.clone(), locals, monomorph_env.clone(), st);
                    emit(st, Instr::SetIdx);
                }
                _ => unimplemented!(),
            },
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), locals, monomorph_env.clone(), st);
                if !is_last {
                    emit(st, Instr::Pop);
                }
            }
            StmtKind::InterfaceImpl(..) => {
                // noop -- handled elsewhere
            }
            StmtKind::FuncDef(..) => {
                // noop -- handled elsewhere
            }
            StmtKind::InterfaceDef(..) | StmtKind::TypeDef(..) => {
                // noop
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
                let resolution = self.statics.name_resolutions.get(&expr.id).unwrap();
                if let Resolution::Var(node_id) = resolution {
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

    fn get_func_definition_node(
        &self,
        method_name: &Symbol,
        desired_interface_impl: SolvedType,
    ) -> NodeId {
        if let Some(interface_name) = self.statics.method_to_interface.get(method_name) {
            let impl_list = self.statics.interface_impls.get(interface_name).unwrap();
            // TODO just because the variable is the same name as an overloaded function doesn't mean the overloaded function is actually being used here.
            // use the type of the variable to determine if it's the same as the overloaded function?

            // find an impl that matches
            // dbg!(impl_list);

            for imp in impl_list {
                for method in &imp.methods {
                    if method.name == *method_name {
                        let method_identifier_node =
                            self.node_map.get(&method.identifier_location).unwrap();

                        let func_id = method_identifier_node.id();
                        let unifvar = self.statics.vars.get(&Prov::Node(func_id)).unwrap();
                        let interface_impl_ty = unifvar.solution().unwrap();

                        if ty_fits_impl_ty(
                            &self.statics,
                            desired_interface_impl.clone(),
                            interface_impl_ty,
                        )
                        .is_ok()
                        {
                            // if desired_interface_impl.clone() == interface_impl_ty {

                            return method.method_location;
                        }
                    }
                }
            }
            panic!("couldn't find impl for method");
        } else {
            panic!("no interface found for method: {}", method_name);
        }
    }

    fn handle_overloaded_func(
        &self,
        st: &mut TranslatorState,
        substituted_ty: SolvedType,
        func_name: &Symbol,
        definition_node: NodeId,
    ) {
        let instance_ty = substituted_ty.monotype().unwrap();
        // println!("instance type: {:?}", &instance_ty);

        let entry = st.overloaded_func_map.entry(OverloadedFuncDesc {
            name: func_name.clone(),
            impl_type: instance_ty.clone(),
            definition_node,
        });
        let label = match entry {
            std::collections::btree_map::Entry::Occupied(o) => o.get().clone(),
            std::collections::btree_map::Entry::Vacant(v) => {
                st.overloaded_methods_to_generate.push((
                    OverloadedFuncDesc {
                        name: func_name.clone(),
                        impl_type: instance_ty.clone(),
                        definition_node,
                    },
                    substituted_ty,
                ));
                let mut label_hint = format!("{}__{}", func_name, instance_ty);
                label_hint.retain(|c| !c.is_whitespace());
                let label = make_label(&label_hint);
                v.insert(label.clone());
                label
            }
        };
        // println!("emitting Call of function: {}", label);
        emit(st, Instr::Call(label));
    }

    fn _display_node(&self, node_id: NodeId) {
        let node = self.node_map.get(&node_id).unwrap();
        let span = node.span();
        let mut s = String::new();
        span.display(&mut s, &self.sources, "");
        println!("{}", s);
    }

    fn handle_pat_binding(&self, pat: Rc<Pat>, locals: &OffsetTable, st: &mut TranslatorState) {
        let _ = self; // avoid warning

        match &*pat.patkind {
            PatKind::Var(_) => {
                // self.display_node(pat.id);
                let idx = locals.get(&pat.id).unwrap();
                emit(st, Instr::StoreOffset(*idx));
            }
            PatKind::Tuple(pats) => {
                emit(st, Instr::Deconstruct);
                for pat in pats.iter() {
                    self.handle_pat_binding(pat.clone(), locals, st);
                }
            }
            PatKind::Variant(_, inner) => {
                if let Some(inner) = inner {
                    // unpack tag and associated data
                    emit(st, Instr::Deconstruct);
                    // pop tag
                    emit(st, Instr::Pop);
                    self.handle_pat_binding(inner.clone(), locals, st);
                } else {
                    emit(st, Instr::Pop);
                }
            }
            PatKind::Unit
            | PatKind::Bool(..)
            | PatKind::Int(..)
            | PatKind::Float(..)
            | PatKind::Str(..)
            | PatKind::Wildcard => {
                emit(st, Instr::Pop);
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
        ExprKind::Array(exprs) => {
            for expr in exprs {
                collect_locals_expr(expr, locals);
            }
        }
        ExprKind::List(exprs) => {
            for expr in exprs {
                collect_locals_expr(expr, locals);
            }
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs {
                collect_locals_expr(expr, locals);
            }
        }
        ExprKind::If(cond, then_block, else_block) => {
            collect_locals_expr(cond, locals);
            collect_locals_expr(then_block, locals);
            if let Some(else_block) = else_block {
                collect_locals_expr(else_block, locals);
            }
        }
        ExprKind::WhileLoop(cond, body) => {
            collect_locals_expr(cond, locals);
            collect_locals_expr(body, locals);
        }
        ExprKind::BinOp(left, _, right) => {
            collect_locals_expr(left, locals);
            collect_locals_expr(right, locals);
        }
        ExprKind::FieldAccess(accessed, _) => {
            collect_locals_expr(accessed, locals);
        }
        ExprKind::IndexAccess(array, index) => {
            collect_locals_expr(array, locals);
            collect_locals_expr(index, locals);
        }
        ExprKind::FuncAp(func, args) => {
            collect_locals_expr(func, locals);
            for arg in args {
                collect_locals_expr(arg, locals);
            }
        }
        ExprKind::Func(..) => {}
        ExprKind::Var(..)
        | ExprKind::Unit
        | ExprKind::Int(..)
        | ExprKind::Float(..)
        | ExprKind::Bool(..)
        | ExprKind::Str(..) => {}
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
            StmtKind::Set(..) => {}
            StmtKind::InterfaceImpl(..) => {}
            StmtKind::FuncDef(..) | StmtKind::TypeDef(..) | StmtKind::InterfaceDef(..) => {}
        }
    }
}

fn collect_locals_pat(pat: Rc<Pat>, locals: &mut HashSet<NodeId>) {
    match &*pat.patkind {
        PatKind::Var(_) => {
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
    format!("{}__#{:X}", hint, id)
}

fn idx_of_field(statics: &StaticsContext, accessed: Rc<Expr>, field: &str) -> u16 {
    let accessed_ty = statics.solution_of_node(accessed.id).unwrap();

    match accessed_ty {
        SolvedType::UdtInstance(symbol, _) => {
            let struct_ty = statics.struct_defs.get(&symbol).expect("not a struct type");
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

fn update_monomorph_env(
    monomorph_env: MonomorphEnv,
    overloaded_ty: SolvedType,
    monomorphic_ty: SolvedType,
) {
    match (overloaded_ty, monomorphic_ty.clone()) {
        // recurse
        (SolvedType::Function(args, out), SolvedType::Function(args2, out2)) => {
            for i in 0..args.len() {
                update_monomorph_env(monomorph_env.clone(), args[i].clone(), args2[i].clone());
            }
            update_monomorph_env(monomorph_env, *out, *out2);
        }
        (SolvedType::UdtInstance(ident, params), SolvedType::UdtInstance(ident2, params2)) => {
            assert_eq!(ident, ident2);
            for i in 0..params.len() {
                update_monomorph_env(monomorph_env.clone(), params[i].clone(), params2[i].clone());
            }
        }
        (SolvedType::Poly(ident, _), _) => {
            monomorph_env.extend(ident, monomorphic_ty);
        }
        (SolvedType::Tuple(elems1), SolvedType::Tuple(elems2)) => {
            for i in 0..elems1.len() {
                update_monomorph_env(monomorph_env.clone(), elems1[i].clone(), elems2[i].clone());
            }
        }
        _ => {}
    }
}

fn subst_with_monomorphic_env(monomorphic_env: MonomorphEnv, ty: SolvedType) -> SolvedType {
    match ty {
        SolvedType::Function(args, out) => {
            let new_args = args
                .iter()
                .map(|arg| subst_with_monomorphic_env(monomorphic_env.clone(), arg.clone()))
                .collect();
            let new_out = subst_with_monomorphic_env(monomorphic_env, *out);
            SolvedType::Function(new_args, Box::new(new_out))
        }
        SolvedType::UdtInstance(ident, params) => {
            let new_params = params
                .iter()
                .map(|param| subst_with_monomorphic_env(monomorphic_env.clone(), param.clone()))
                .collect();
            SolvedType::UdtInstance(ident, new_params)
        }
        SolvedType::Poly(ref ident, _) => {
            if let Some(monomorphic_ty) = monomorphic_env.lookup(ident) {
                monomorphic_ty
            } else {
                ty
            }
        }
        SolvedType::Tuple(elems) => {
            let new_elems = elems
                .iter()
                .map(|elem| subst_with_monomorphic_env(monomorphic_env.clone(), elem.clone()))
                .collect();
            SolvedType::Tuple(new_elems)
        }
        _ => ty,
    }
}
