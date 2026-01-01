/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::assembly::{Instr, Label, Line, LineVariant, Reg, remove_labels_and_constants};
use crate::ast::{
    ArgMaybeAnnotated, AssignOperator, AstNode, BinaryOperator, FuncDecl, FuncDef, InterfaceDef,
    ItemKind,
};
use crate::ast::{FileAst, NodeId};
use crate::environment::Environment;
use crate::intrinsic::IntrinsicOperation;
use crate::optimize_bytecode::optimize;
use crate::parse::PrefixOp;
use crate::statics::typecheck::Nominal;
use crate::statics::typecheck::SolvedType;
use crate::statics::{Declaration, PolytypeDeclaration, TypeProv};
use crate::statics::{FuncResolutionKind, Type};
use crate::vm::{AbraInt, Instr as VmInstr};
use crate::{
    ast::{Expr, ExprKind, Pat, PatKind, Stmt, StmtKind},
    statics::StaticsContext,
};
use std::mem;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use utils::hash::HashMap;
use utils::hash::HashSet;
use utils::id_set::IdSet;
use utils::swrite;

type OffsetTable = HashMap<NodeId, i16>;
type MonomorphEnv = Environment<PolytypeDeclaration, Type>;
pub(crate) type LabelMap = HashMap<Label, usize>;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
struct FuncDesc {
    kind: FuncKind,
    overload_ty: Option<SolvedType>,
}

impl FuncDesc {
    fn unqualified_name(&self) -> String {
        match &self.kind {
            FuncKind::NamedFunc(f) => f.name.v.clone(),
            FuncKind::AnonymousFunc { .. } => "<lambda>".to_string(),
            FuncKind::IntrinsicWrapper(b, _) => b.name(),
            FuncKind::ForeignFunctionWrapper { func_decl, .. } => func_decl.name.v.clone(),
            FuncKind::HostFunctionWrapper(f) => f.name.v.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
enum FuncKind {
    NamedFunc(Rc<FuncDef>),
    AnonymousFunc {
        lambda: Rc<Expr>,
        capture_types: Vec<SolvedType>, // TODO: don't store this in here, just calculate it using the `lambda` field. (and should be memoizing calculation of captures)
        capture_types_concrete: Vec<SolvedType>,
    },
    IntrinsicWrapper(IntrinsicOperation, AstNode),
    ForeignFunctionWrapper {
        func_decl: Rc<FuncDecl>,
        libname: PathBuf,
        symbol: String,
    },
    HostFunctionWrapper(Rc<FuncDecl>),
}

pub(crate) struct Translator {
    statics: StaticsContext,
    file_asts: Vec<Rc<FileAst>>,
}

#[derive(Debug, Default)]
pub(crate) struct TranslatorState {
    lines: Vec<Line>,
    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,
    function_name_arena: IdSet<String>,
    instr_count: usize,
    func_map: HashMap<FuncDesc, Label>,
    funcs_to_generate: Vec<FuncDesc>,
    loop_stack: Vec<EnclosingLoop>,
    return_stack: Vec<u32>,

    pub(crate) curr_file: u32,
    pub(crate) curr_func: u32,
    pub(crate) curr_lineno: usize,
}

#[derive(Debug, Default)]
struct EnclosingLoop {
    start_label: String,
    end_label: String,
}

#[derive(Default)]
pub(crate) struct ConstantsHolder {
    pub(crate) int_constants: IdSet<AbraInt>,
    pub(crate) float_constants: IdSet<String>,
    pub(crate) string_constants: IdSet<String>,
}

fn gather_constants(lines: &Vec<Line>) -> ConstantsHolder {
    let mut constants = ConstantsHolder::default();
    for line in lines {
        if let Line::Instr { instr, .. } = line {
            match instr {
                Instr::PushInt(i) => {
                    constants.int_constants.insert(*i);
                }
                Instr::PushFloat(f) => {
                    constants.float_constants.insert(f.clone());
                }
                Instr::PushString(s) => {
                    constants.string_constants.insert(s.clone());
                }
                Instr::StoreOffsetImm(_, imm)
                | Instr::AddIntImm(_, _, imm)
                | Instr::SubIntImm(_, _, imm)
                | Instr::MulIntImm(_, _, imm)
                | Instr::DivIntImm(_, _, imm)
                | Instr::PowIntImm(_, _, imm)
                | Instr::ModuloImm(_, _, imm)
                | Instr::LessThanIntImm(_, _, imm)
                | Instr::LessThanOrEqualIntImm(_, _, imm)
                | Instr::GreaterThanIntImm(_, _, imm)
                | Instr::GreaterThanOrEqualIntImm(_, _, imm)
                | Instr::EqualIntImm(_, _, imm)
                | Instr::ArrayPushIntImm(_, imm) => {
                    constants.int_constants.insert(*imm);
                }
                Instr::AddFloatImm(_, _, imm)
                | Instr::SubFloatImm(_, _, imm)
                | Instr::MulFloatImm(_, _, imm)
                | Instr::DivFloatImm(_, _, imm)
                | Instr::PowFloatImm(_, _, imm)
                | Instr::LessThanFloatImm(_, _, imm)
                | Instr::LessThanOrEqualFloatImm(_, _, imm)
                | Instr::GreaterThanFloatImm(_, _, imm)
                | Instr::GreaterThanOrEqualFloatImm(_, _, imm)
                | Instr::EqualFloatImm(_, _, imm) => {
                    constants.float_constants.insert(imm.clone());
                }
                _ => {}
            }
        }
    }
    constants
}

#[derive(Debug, Clone)]
pub struct CompiledProgram {
    pub(crate) instructions: Vec<VmInstr>,
    pub(crate) int_constants: Vec<AbraInt>,
    pub(crate) float_constants: Vec<f64>,
    pub(crate) static_strings: Vec<String>,
    // debug data
    pub(crate) filename_arena: Vec<String>,
    pub(crate) function_name_arena: Vec<String>,
    pub(crate) filename_table: Vec<(BytecodeIndex, u32)>,
    pub(crate) lineno_table: Vec<(BytecodeIndex, u32)>,
    pub(crate) function_name_table: Vec<(BytecodeIndex, u32)>,
}

pub type BytecodeIndex = u32;

impl Translator {
    pub(crate) fn new(statics: StaticsContext, file_asts: Vec<Rc<FileAst>>) -> Self {
        Self { statics, file_asts }
    }

    fn get_ty(&self, mono: &MonomorphEnv, node: AstNode) -> Option<SolvedType> {
        self.statics.solution_of_node(node).map(|t| t.subst(mono))
    }

    fn emit(&self, st: &mut TranslatorState, i: impl LineVariant) {
        let l: Line = i.to_line(st);

        if let Line::Instr { .. } = &l {
            st.instr_count += 1;
        }

        st.lines.push(l);
    }

    fn create_source_location_tables(&self, st: &mut TranslatorState) {
        let mut bytecode_index = 0;
        for line in &st.lines {
            if let Line::Instr {
                instr: _,
                lineno,
                file_id,
                func_id,
            } = line
            {
                // file
                {
                    let mut redundant = false;
                    if let Some(last) = st.filename_table.last()
                        && last.1 == *file_id
                    {
                        redundant = true;
                    }
                    if !redundant {
                        st.filename_table.push((bytecode_index as u32, *file_id));
                    }
                }
                // lineno
                {
                    let mut redundant = false;
                    if let Some(last) = st.lineno_table.last()
                        && last.1 == *lineno as u32
                    {
                        redundant = true;
                    }
                    if !redundant {
                        st.lineno_table
                            .push((bytecode_index as u32, *lineno as u32));
                    }
                }
                // func
                {
                    let mut redundant = false;
                    if let Some(last) = st.function_name_table.last()
                        && last.1 == *func_id
                    {
                        redundant = true;
                    }
                    if !redundant {
                        st.function_name_table
                            .push((bytecode_index as u32, *func_id));
                    }
                }

                bytecode_index += 1;
            }
        }
    }

    fn update_current_file_and_lineno(&self, st: &mut TranslatorState, node: AstNode) {
        let location = node.location();
        let file_id = location.file_id;

        let file = self.statics.file_db.get(file_id).unwrap();
        let line_no = file.line_number_for_index(location.lo);
        st.curr_file = file_id;
        st.curr_lineno = line_no;
    }

    fn update_curr_function(&self, st: &mut TranslatorState, name: &str) {
        let function_name_id = st.function_name_arena.insert(name.to_string());
        st.curr_func = function_name_id;
    }

    pub(crate) fn translate(&self) -> CompiledProgram {
        let mut st = self.translate_to_assembly();

        self.create_source_location_tables(&mut st);
        let constants = gather_constants(&st.lines);
        let (instructions, _) = remove_labels_and_constants(&st.lines, &constants);
        let mut filename_arena = vec![];
        for file_data in self.statics.file_db.files.iter() {
            filename_arena.push(file_data.name().to_string());
        }
        CompiledProgram {
            instructions,
            int_constants: constants.int_constants.into_iter().collect(),
            float_constants: constants
                .float_constants
                .clone()
                .into_iter()
                .map(|s| s.parse::<f64>().unwrap())
                .collect(),
            static_strings: constants.string_constants.clone().into_iter().collect(),
            filename_arena,
            function_name_arena: st.function_name_arena.into_iter().collect(),
            filename_table: st.filename_table,
            lineno_table: st.lineno_table,
            function_name_table: st.function_name_table,
        }
    }

    pub(crate) fn dump_assembly(&self) {
        let st = self.translate_to_assembly();
        for line in st.lines.iter() {
            println!("{}", line);
        }
    }

    fn translate_to_assembly(&self) -> TranslatorState {
        let mut st = TranslatorState::default();
        {
            let st = &mut st;

            let mono = MonomorphEnv::empty();

            // Initialization routine before main function (load shared libraries)
            for (i, lib) in self.statics.dylibs.iter().enumerate() {
                self.emit(st, Instr::PushString(lib.to_str().unwrap().to_string()));
                self.emit(st, Instr::LoadLib);
                for s in self.statics.dylib_to_funcs[&(i as u32)].iter() {
                    self.emit(st, Instr::PushString(s.to_string()));
                    self.emit(st, Instr::LoadForeignFunc);
                }
            }

            // Handle the main function (files)
            if let Some(file) = self.file_asts.first() {
                let mut locals = HashSet::default();

                // use filename as name of function in this case
                self.update_curr_function(st, "<main>");

                let stmts: Vec<_> = file
                    .items
                    .iter()
                    .filter_map(|item| match &*item.kind {
                        ItemKind::Stmt(stmt) => Some(stmt.clone()),
                        _ => None,
                    })
                    .collect();
                self.collect_locals_stmts(&stmts, &mut locals, &mono);

                self.emit(st, Instr::PushNil(locals.len() as u16));
                let mut offset_table = OffsetTable::default();
                for (offset, node_id) in locals.iter().enumerate() {
                    offset_table.entry(node_id.id()).or_insert(offset as i16);
                }

                let statements = file
                    .items
                    .iter()
                    .filter_map(|item| match &*item.kind {
                        ItemKind::Stmt(stmt) => Some(stmt),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                for (i, stmt) in statements.iter().enumerate() {
                    self.translate_stmt(stmt, i == statements.len() - 1, &offset_table, &mono, st);
                }

                self.emit(st, Instr::Stop);
            }

            while !st.funcs_to_generate.is_empty() {
                // Generate bytecode for function bodies
                let mut iteration = Vec::new();
                mem::swap(&mut (iteration), &mut st.funcs_to_generate);
                for desc in iteration {
                    self.update_curr_function(st, &desc.unqualified_name());

                    let label = st.func_map.get(&desc).unwrap();
                    self.emit(st, Line::Label(label.clone()));
                    match &desc.kind {
                        FuncKind::NamedFunc(f) => {
                            let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
                            self.translate_func_body_helper(
                                st,
                                MonomorphEnv::empty(),
                                &desc,
                                func_ty,
                                &f.args,
                                &f.body,
                            );
                        }
                        FuncKind::AnonymousFunc {
                            lambda: e,
                            capture_types,
                            capture_types_concrete,
                        } => {
                            let ExprKind::AnonymousFunction(args, _, body) = &*e.kind else {
                                unreachable!()
                            };

                            let func_ty = self.statics.solution_of_node(e.node()).unwrap();
                            let mono_for_lambda = MonomorphEnv::empty();
                            if capture_types.iter().any(|ty| ty.is_overloaded()) {
                                for (overloaded_ty, ty_concrete) in
                                    capture_types.iter().zip(capture_types_concrete.iter())
                                {
                                    mono_for_lambda.update(overloaded_ty, ty_concrete);
                                }
                            }
                            self.translate_func_body_helper(
                                st,
                                mono_for_lambda,
                                &desc,
                                func_ty,
                                args,
                                body,
                            );
                        }
                        FuncKind::IntrinsicWrapper(b, func_node) => {
                            self.emit_intrinsic(st, &mono, *b, func_node.clone(), true);
                        }
                        FuncKind::ForeignFunctionWrapper {
                            func_decl,
                            libname,
                            symbol,
                        } => {
                            self.emit_foreign(st, func_decl, libname, symbol, true);
                        }
                        FuncKind::HostFunctionWrapper(f) => {
                            self.emit_host(st, f, true);
                        }
                    };
                }
            }
        }

        st.lines = optimize(st.lines);

        st
    }

    fn translate_func_body_helper(
        &self,
        st: &mut TranslatorState,
        mono: MonomorphEnv,
        desc: &FuncDesc,
        func_ty: SolvedType,
        args: &[ArgMaybeAnnotated],
        body: &Rc<Expr>,
    ) {
        if let Some(overload_ty) = &desc.overload_ty {
            mono.update(&func_ty, overload_ty);
        }

        let (arg_ids, captures, locals) =
            self.calculate_args_captures_locals(&desc.overload_ty, args, body, &mono);
        self.emit(st, Instr::PushNil(locals.len() as u16));
        let mut offset_table = OffsetTable::default();
        for (index, arg_id) in arg_ids.iter().enumerate() {
            offset_table
                .entry(arg_id.id())
                .or_insert(-(index as i16) - 1);
        }
        for (i, capture) in captures.iter().enumerate() {
            offset_table.entry(capture.id()).or_insert(i as i16);
        }
        for (i, local) in locals.iter().enumerate() {
            offset_table
                .entry(local.id())
                .or_insert((i + captures.len()) as i16);
        }
        let nargs = arg_ids.len();
        st.return_stack.push(nargs as u32);
        self.translate_expr(body, &offset_table, &mono, st);
        st.return_stack.pop();

        let SolvedType::Function(_, out_ty) = func_ty else { unreachable!() };
        if *out_ty == SolvedType::Void {
            self.emit(st, Instr::ReturnVoid);
        } else {
            self.emit(st, Instr::Return(nargs as u32));
        }
    }

    fn translate_expr(
        &self,
        expr: &Rc<Expr>,
        offset_table: &OffsetTable,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_current_file_and_lineno(st, expr.node());

        match &*expr.kind {
            ExprKind::Variable(_) => self.translate_declaration(
                &self.statics.resolution_map[&expr.id],
                expr.node(),
                offset_table,
                mono,
                st,
            ),
            ExprKind::MemberAccessLeadingDot(ident) => match self.statics.resolution_map[&ident.id]
            {
                Declaration::EnumVariant { variant, .. } => {
                    self.emit(st, Instr::PushNil(1));
                    self.emit(
                        st,
                        Instr::ConstructVariant {
                            tag: variant as u16,
                        },
                    );
                }
                _ => panic!(),
            },
            ExprKind::Nil => {}
            ExprKind::Bool(b) => {
                self.emit(st, Instr::PushBool(*b));
            }
            ExprKind::Int(i) => {
                self.emit(st, Instr::PushInt(*i));
            }
            ExprKind::Float(f) => {
                self.emit(st, Instr::PushFloat(f.clone()));
            }
            ExprKind::Str(s) => {
                self.emit(st, Instr::PushString(s.clone()));
            }
            ExprKind::BinOp(left, op, right) => {
                self.translate_expr(left, offset_table, mono, st);
                match op {
                    BinaryOperator::Or => {
                        let short_circuit = make_label("short_circuit_or");
                        let end_label = make_label("end_or");
                        self.emit(st, Instr::JumpIf(short_circuit.clone()));
                        self.translate_expr(right, offset_table, mono, st);
                        self.emit(st, Instr::Jump(end_label.clone()));
                        self.emit(st, short_circuit);
                        self.emit(st, Instr::PushBool(true));
                        self.emit(st, end_label);
                        return;
                    }
                    BinaryOperator::And => {
                        let short_circuit = make_label("short_circuit_and");
                        let end_label = make_label("end_and");
                        self.emit(st, Instr::JumpIfFalse(short_circuit.clone()));
                        self.translate_expr(right, offset_table, mono, st);
                        self.emit(st, Instr::Jump(end_label.clone()));
                        self.emit(st, short_circuit);
                        self.emit(st, Instr::PushBool(false));
                        self.emit(st, end_label);
                        return;
                    }
                    _ => {}
                };
                self.translate_expr(right, offset_table, mono, st);
                let mut helper = |mono: &MonomorphEnv, method_name: &str| {
                    let iface_method = self
                        .statics
                        .root_namespace
                        .get_declaration(method_name)
                        .unwrap();
                    let Declaration::InterfaceMethod {
                        method,
                        iface: iface_def,
                    } = iface_method
                    else {
                        unreachable!()
                    };
                    let arg1_ty = self.get_ty(mono, left.node()).unwrap();
                    let arg2_ty = self.get_ty(mono, right.node()).unwrap();
                    let out_ty = self.get_ty(mono, expr.node()).unwrap();
                    let func_ty = Type::Function(vec![arg1_ty, arg2_ty], out_ty.into());

                    self.translate_iface_method_ap_helper(
                        st,
                        mono,
                        &iface_def,
                        method as u16,
                        &func_ty,
                    );
                };
                let arg1_ty = self.get_ty(mono, left.node()).unwrap();
                // inline primitive operations instead of performing a function call
                match op {
                    BinaryOperator::Add => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::AddInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::AddFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
                    },
                    BinaryOperator::Subtract => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::SubInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::SubFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
                    },
                    BinaryOperator::Multiply => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::MulInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::MulFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
                    },
                    BinaryOperator::Divide => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::DivInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::DivFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
                    },
                    BinaryOperator::GreaterThan => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::GreaterThanInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::GreaterThanFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => {
                            helper(mono, "prelude.Ord.greater_than");
                        }
                    },
                    BinaryOperator::LessThan => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::LessThanInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::LessThanFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => {
                            helper(mono, "prelude.Ord.less_than");
                        }
                    },
                    BinaryOperator::GreaterThanOrEqual => match arg1_ty {
                        SolvedType::Int => self.emit(
                            st,
                            Instr::GreaterThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top),
                        ),
                        SolvedType::Float => self.emit(
                            st,
                            Instr::GreaterThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                        ),
                        _ => {
                            helper(mono, "prelude.Ord.greater_than_or_equal");
                        }
                    },
                    BinaryOperator::LessThanOrEqual => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::LessThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => self.emit(
                            st,
                            Instr::LessThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                        ),
                        _ => {
                            helper(mono, "prelude.Ord.less_than_or_equal");
                        }
                    },
                    BinaryOperator::Equal | BinaryOperator::NotEqual => {
                        match arg1_ty {
                            SolvedType::Int => {
                                self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top))
                            }
                            SolvedType::Float => {
                                self.emit(st, Instr::EqualFloat(Reg::Top, Reg::Top, Reg::Top))
                            }
                            SolvedType::Bool => {
                                self.emit(st, Instr::EqualBool(Reg::Top, Reg::Top, Reg::Top))
                            }
                            SolvedType::String => {
                                self.emit(st, Instr::EqualString(Reg::Top, Reg::Top, Reg::Top))
                            }
                            _ => {
                                helper(mono, "prelude.Equal.equal");
                            }
                        }
                        if *op == BinaryOperator::NotEqual {
                            self.emit(st, Instr::Not(Reg::Top, Reg::Top));
                        }
                    }
                    BinaryOperator::Pow => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::PowInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::PowFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
                    },
                    BinaryOperator::Format => {
                        let format_append_decl = self
                            .statics
                            .root_namespace
                            .get_declaration("prelude.format_append")
                            .unwrap();
                        let Declaration::FreeFunction(FuncResolutionKind::Ordinary(func_def)) =
                            format_append_decl
                        else {
                            unreachable!()
                        };
                        let func_name = &self.statics.fully_qualified_names[&func_def.name.id];

                        let arg2_ty = self.get_ty(mono, right.node()).unwrap();
                        let out_ty = self.get_ty(mono, expr.node()).unwrap();
                        let specific_func_ty =
                            Type::Function(vec![arg1_ty, arg2_ty], out_ty.into());

                        self.handle_func_call(
                            st,
                            mono,
                            Some(specific_func_ty),
                            func_name,
                            &func_def,
                        );
                    }
                    BinaryOperator::Or => unreachable!(),
                    BinaryOperator::And => unreachable!(),
                    BinaryOperator::Mod => {
                        self.emit(st, Instr::Modulo(Reg::Top, Reg::Top, Reg::Top))
                    }
                }
            }
            ExprKind::Unop(op, right) => {
                let arg1_ty = self.get_ty(mono, right.node()).unwrap();
                // inline primitive operations instead of performing a function call
                match op {
                    PrefixOp::Minus => match arg1_ty {
                        SolvedType::Int => {
                            // TODO: does this get optimized?
                            self.emit(st, Instr::PushInt(0));
                            self.translate_expr(right, offset_table, mono, st);
                            self.emit(st, Instr::SubInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::PushInt(0));
                            self.translate_expr(right, offset_table, mono, st);
                            self.emit(st, Instr::SubFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
                    },
                    PrefixOp::Not => {
                        self.translate_expr(right, offset_table, mono, st);
                        self.emit(st, Instr::Not(Reg::Top, Reg::Top));
                    }
                }
            }
            ExprKind::FuncAp(func, args) => {
                match &*func.kind {
                    ExprKind::Variable(_) => {
                        for arg in args {
                            self.translate_expr(arg, offset_table, mono, st);
                        }
                        let decl = &self.statics.resolution_map[&func.id];
                        self.translate_func_ap(decl, func.node(), offset_table, mono, st);
                    }
                    ExprKind::MemberAccess(receiver_expr, fname) => {
                        self.translate_expr(receiver_expr, offset_table, mono, st);
                        for arg in args {
                            self.translate_expr(arg, offset_table, mono, st);
                        }

                        let decl = &self.statics.resolution_map[&fname.id];
                        self.translate_func_ap(decl, fname.node(), offset_table, mono, st);
                    }
                    ExprKind::MemberAccessLeadingDot(fname) => {
                        for arg in args {
                            self.translate_expr(arg, offset_table, mono, st);
                        }

                        let decl = &self.statics.resolution_map[&fname.id];
                        self.translate_func_ap(decl, fname.node(), offset_table, mono, st);
                    }

                    ExprKind::Nil
                    | ExprKind::Int(_)
                    | ExprKind::Float(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Str(_)
                    | ExprKind::Array(_)
                    | ExprKind::Tuple(..) => {
                        unreachable!("lhs of FuncAp can't possibly be a function")
                    }

                    ExprKind::BinOp(..)
                    | ExprKind::Unop(..)
                    | ExprKind::Unwrap(..)
                    | ExprKind::IfElse(..)
                    | ExprKind::Match(..)
                    | ExprKind::Block(..)
                    | ExprKind::IndexAccess(..)
                    | ExprKind::FuncAp(..)
                    | ExprKind::AnonymousFunction(..) => {
                        for arg in args {
                            self.translate_expr(arg, offset_table, mono, st);
                        }
                        self.translate_expr(func, offset_table, mono, st);
                        self.translate_lambda_ap(st, mono, func.node());
                    }
                };
            }
            ExprKind::Block(statements) => {
                for (i, statement) in statements.iter().enumerate() {
                    self.translate_stmt(
                        statement,
                        i == statements.len() - 1,
                        offset_table,
                        mono,
                        st,
                    );
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr, offset_table, mono, st);
                }
                let mut nargs = 0;
                for expr in exprs {
                    // TODO: duplicated logic
                    let expr_ty = self.get_ty(mono, expr.node()).unwrap();
                    if expr_ty != SolvedType::Void {
                        nargs += 1;
                    }
                }
                self.emit(st, Instr::ConstructStruct(nargs));
            }
            ExprKind::IfElse(cond, then_block, else_block) => {
                self.translate_expr(cond, offset_table, mono, st);
                let else_label = make_label("else");
                let end_label = make_label("endif");
                self.emit(st, Instr::JumpIfFalse(else_label.clone()));
                self.translate_stmt(then_block, true, offset_table, mono, st);
                self.emit(st, Instr::Jump(end_label.clone()));
                self.emit(st, Line::Label(else_label));
                if let Some(else_block) = else_block {
                    self.translate_stmt(else_block, true, offset_table, mono, st);
                }
                self.emit(st, Line::Label(end_label));
            }
            ExprKind::MemberAccess(accessed, field_name) => {
                if let Some(Declaration::EnumVariant { variant, .. }) =
                    &self.statics.resolution_map.get(&field_name.id)
                {
                    self.emit(st, Instr::PushNil(1));
                    self.emit(
                        st,
                        Instr::ConstructVariant {
                            tag: *variant as u16,
                        },
                    );
                } else if let Some(
                    decl @ (Declaration::MemberFunction(..) | Declaration::InterfaceMethod { .. }),
                ) = &self.statics.resolution_map.get(&field_name.id)
                {
                    // member function
                    self.translate_declaration(decl, field_name.node(), offset_table, mono, st);
                } else {
                    let expr_ty = self.get_ty(mono, expr.node()).unwrap();
                    if expr_ty != SolvedType::Void {
                        self.translate_expr(accessed, offset_table, mono, st);
                        let idx = self.idx_of_field(&self.statics, mono, accessed, &field_name.v);
                        self.emit(st, Instr::GetField(idx, Reg::Top));
                    }
                }
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr, offset_table, mono, st);
                }
                if let Some(expr) = exprs.first()
                    && self.get_ty(mono, expr.node()).unwrap() == SolvedType::Void
                {
                    self.emit(st, Instr::PushNil(exprs.len() as u16));
                }
                self.emit(st, Instr::ConstructArray(exprs.len() as u16));
            }
            ExprKind::IndexAccess(array, index) => {
                self.translate_expr(index, offset_table, mono, st);
                self.translate_expr(array, offset_table, mono, st);
                self.emit(st, Instr::GetIndex(Reg::Top, Reg::Top));
            }
            ExprKind::Match(expr, arms) => {
                let ty = self.get_ty(mono, expr.node()).unwrap();

                self.translate_expr(expr, offset_table, mono, st);
                let end_label = make_label("endmatch");
                // Check scrutinee against each arm's pattern
                let arm_labels = arms
                    .iter()
                    .enumerate()
                    .map(|(i, _)| make_label(&format!("arm{i}")))
                    .collect::<Vec<_>>();
                for (i, arm) in arms.iter().enumerate() {
                    let arm_label = arm_labels[i].clone();

                    // duplicate the scrutinee before doing a comparison
                    self.emit(st, Instr::Duplicate);
                    self.translate_pat_comparison(&ty, &arm.pat, st, mono);
                    self.emit(st, Instr::JumpIf(arm_label));
                }
                for (i, arm) in arms.iter().enumerate() {
                    self.emit(st, Line::Label(arm_labels[i].clone()));

                    self.handle_pat_binding(&arm.pat, offset_table, st, mono);

                    self.translate_stmt(&arm.stmt, true, offset_table, mono, st);
                    if i != arms.len() - 1 {
                        self.emit(st, Instr::Jump(end_label.clone()));
                    }
                }
                self.emit(st, Line::Label(end_label));
            }
            ExprKind::AnonymousFunction(args, _, body) => {
                let func_ty = self.statics.solution_of_node(expr.node()).unwrap();
                let overload_ty = if !func_ty.is_overloaded() {
                    None
                } else {
                    let substituted_ty = func_ty.subst(mono);
                    Some(substituted_ty)
                };

                let func_name = "lambda".to_string();

                let (_, captures, _locals) =
                    self.calculate_args_captures_locals(&overload_ty, args, body, mono);

                let desc = FuncDesc {
                    kind: FuncKind::AnonymousFunc {
                        lambda: expr.clone(),
                        capture_types: captures
                            .iter()
                            .cloned()
                            .map(|capture| self.statics.solution_of_node(capture).unwrap())
                            .collect(),
                        capture_types_concrete: captures
                            .iter()
                            .cloned()
                            .map(|capture| self.get_ty(mono, capture).unwrap())
                            .collect(),
                    },
                    overload_ty: overload_ty.clone(),
                };
                let label = self.get_func_label(st, desc, &func_name);

                self.emit(st, Instr::PushAddr(label.clone()));
                for capture in &captures {
                    let offs = offset_table.get(&capture.id()).unwrap();
                    self.emit(st, Instr::LoadOffset(*offs));
                }

                self.emit(st, Instr::MakeClosure(captures.len() as u16));
            }
            ExprKind::Unwrap(expr) => {
                self.translate_expr(expr, offset_table, mono, st);

                let Some(func_decl @ Declaration::FreeFunction(FuncResolutionKind::Ordinary(f))) =
                    &self
                        .statics
                        .root_namespace
                        .get_declaration("prelude.unwrap")
                else {
                    panic!();
                };
                // TODO: this would be easier if the postfix unwrap operator had a dedicated AST node and its own type. Then we wouldn't have to do this weird hack here
                let expr_ty = self.get_ty(mono, expr.node()).unwrap();
                let ret_ty = f
                    .ret_type
                    .clone()
                    .unwrap()
                    .to_solved_type(&self.statics)
                    .unwrap();
                mono.update(&ret_ty, &expr_ty);
                self.translate_func_ap(func_decl, f.name.node(), offset_table, mono, st);
            }
        }
    }

    fn translate_declaration(
        &self,
        decl: &Declaration,
        ast_node: AstNode,
        offset_table: &OffsetTable,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        match decl {
            Declaration::EnumVariant { variant, .. } => {
                self.emit(st, Instr::PushNil(1)); // TODO: optimize this away
                self.emit(
                    st,
                    Instr::ConstructVariant {
                        tag: *variant as u16,
                    },
                );
            }
            Declaration::Var(node) => {
                let expr_ty = self.get_ty(mono, ast_node).unwrap();
                if expr_ty != SolvedType::Void {
                    let idx = offset_table.get(&node.id()).unwrap();
                    self.emit(st, Instr::LoadOffset(*idx));
                }
            }
            Declaration::Intrinsic(b) => {
                let func_ty = b.type_signature().solution().unwrap();
                let overload_ty = if !func_ty.is_overloaded() {
                    None
                } else {
                    let substituted_ty = self.get_ty(mono, ast_node.clone()).unwrap();
                    Some(substituted_ty)
                };
                let desc = FuncDesc {
                    kind: FuncKind::IntrinsicWrapper(*b, ast_node),
                    overload_ty,
                };
                let label = self.get_func_label(st, desc, &b.name());
                self.emit(st, Instr::PushAddr(label.clone()));
                self.emit(st, Instr::MakeClosure(0));
            }

            Declaration::FreeFunction(FuncResolutionKind::Ordinary(f))
            | Declaration::MemberFunction(f) => {
                let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
                let overload_ty = if !func_ty.is_overloaded() {
                    None
                } else {
                    let substituted_ty = self.get_ty(mono, ast_node).unwrap();
                    Some(substituted_ty)
                };

                let func_name = &self.statics.fully_qualified_names[&f.name.id];
                let desc = FuncDesc {
                    kind: FuncKind::NamedFunc(f.clone()),
                    overload_ty: overload_ty.clone(),
                };

                let label = self.get_func_label(st, desc, func_name);
                self.emit(st, Instr::PushAddr(label.clone()));
                self.emit(st, Instr::MakeClosure(0));
            }

            Declaration::InterfaceMethod { iface, method } => {
                let overload_ty = self.get_ty(mono, ast_node).unwrap();

                let method = &iface.methods[*method].name;
                // TODO this logic is duplicated elsewhere and also looks really inefficient
                let impl_list = &self.statics.interface_impls[iface];
                for imp in impl_list {
                    for func_def in &imp.methods {
                        if func_def.name.v == *method.v {
                            let unifvar = self
                                .statics
                                .unifvars
                                .get(&TypeProv::Node(func_def.name.node()))
                                .unwrap();
                            let interface_impl_ty = unifvar.solution().unwrap();

                            if overload_ty.fits_impl_ty(&self.statics, &interface_impl_ty) {
                                let func_name = &self.statics.fully_qualified_names[&method.id];
                                let desc = FuncDesc {
                                    kind: FuncKind::NamedFunc(func_def.clone()),
                                    overload_ty: Some(overload_ty.clone()),
                                };

                                let label = self.get_func_label(st, desc, func_name);
                                self.emit(st, Instr::PushAddr(label.clone()));
                                self.emit(st, Instr::MakeClosure(0));
                                return;
                            }
                        }
                    }
                }

                panic!();
            }
            Declaration::FreeFunction(FuncResolutionKind::Host(f)) => {
                let desc = FuncDesc {
                    kind: FuncKind::HostFunctionWrapper(f.clone()),
                    overload_ty: None,
                };
                let label = self.get_func_label(st, desc, &f.name.v);
                self.emit(st, Instr::PushAddr(label.clone()));
                self.emit(st, Instr::MakeClosure(0));
            }
            Declaration::FreeFunction(FuncResolutionKind::_Foreign {
                decl: func_decl,
                libname,
                symbol,
            }) => {
                let desc = FuncDesc {
                    kind: FuncKind::ForeignFunctionWrapper {
                        func_decl: func_decl.clone(),
                        libname: libname.clone(),
                        symbol: symbol.clone(),
                    },
                    overload_ty: None,
                };
                let label = self.get_func_label(st, desc, &func_decl.name.v);
                self.emit(st, Instr::PushAddr(label.clone()));
                self.emit(st, Instr::MakeClosure(0));
            }
            Declaration::Struct(_)
            | Declaration::Enum { .. }
            | Declaration::Array
            | Declaration::InterfaceDef(_)
            | Declaration::Namespace(_) => {
                // noop, does not exist at runtime
                //
                // Person.fullname(my_person)
                // ^^^^^
                // Clone.clone(my_array)
                // ^^^^^
                // array.push
                // ^^^^^
            }

            Declaration::Polytype(_)
            | Declaration::InterfaceOutputType { .. }
            | Declaration::BuiltinType(_) => {
                unreachable!()
            }
        }
    }

    fn translate_lambda_ap(&self, st: &mut TranslatorState, mono: &MonomorphEnv, node: AstNode) {
        let Some(SolvedType::Function(args, _)) = self.get_ty(mono, node.clone()) else {
            unreachable!()
        };
        let nargs = args.iter().filter(|arg| **arg != SolvedType::Void).count();
        self.emit(st, Instr::CallFuncObj(nargs as u32));
    }

    // used for free functions and member functions
    fn translate_func_ap_helper(
        &self,
        f: &Rc<FuncDef>,
        f_fully_qualified_name: &String,
        func_node: AstNode,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
        if !func_ty.is_overloaded() {
            self.handle_func_call(st, mono, None, f_fully_qualified_name, f);
        } else {
            let func_instance_ty = self.get_ty(mono, func_node).unwrap();
            self.handle_func_call(st, mono, Some(func_instance_ty), f_fully_qualified_name, f);
        }
    }

    // used for interface methods
    fn translate_iface_method_ap_helper(
        &self,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
        iface_def: &Rc<InterfaceDef>,
        method_index: u16,
        func_ty: &SolvedType,
    ) {
        let substituted_ty = func_ty.subst(mono);
        let method = &iface_def.methods[method_index as usize].name;
        let impl_list = &self.statics.interface_impls[iface_def];

        for imp in impl_list {
            for f in &imp.methods {
                if f.name.v == *method.v {
                    let unifvar = self
                        .statics
                        .unifvars
                        .get(&TypeProv::Node(f.name.node()))
                        .unwrap();
                    let interface_impl_ty = unifvar.solution().unwrap();

                    if substituted_ty.fits_impl_ty(&self.statics, &interface_impl_ty) {
                        let fully_qualified_name = &self.statics.fully_qualified_names[&method.id];
                        self.handle_func_call(
                            st,
                            mono,
                            Some(substituted_ty.clone()),
                            fully_qualified_name,
                            f,
                        );
                        return;
                    }
                }
            }
        }
        unreachable!(
            "interface method call could not be translated. There is a bug with the typechecker. interface = {}. method = {}",
            iface_def.name.v, iface_def.methods[method_index as usize].name.v
        )
    }

    fn translate_func_ap(
        &self,
        decl: &Declaration,
        func_node: AstNode,
        offset_table: &OffsetTable,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        match decl {
            Declaration::Var(node) => {
                // assume it's a function object
                let idx = offset_table.get(&node.id()).unwrap();
                self.emit(st, Instr::LoadOffset(*idx));
                self.translate_lambda_ap(st, mono, node.clone());
            }
            Declaration::FreeFunction(FuncResolutionKind::Ordinary(f)) => {
                let f_fully_qualified_name = &self.statics.fully_qualified_names[&f.name.id];
                self.translate_func_ap_helper(f, f_fully_qualified_name, func_node, mono, st);
            }
            Declaration::FreeFunction(FuncResolutionKind::Host(decl)) => {
                let idx = self.statics.host_funcs.get_id(decl) as u16;
                self.emit(st, Instr::HostFunc(idx));
            }
            Declaration::FreeFunction(FuncResolutionKind::_Foreign {
                decl: func_decl,
                libname,
                symbol,
            }) => {
                self.emit_foreign(st, func_decl, libname, symbol, false);
            }
            Declaration::InterfaceMethod {
                iface: iface_def,
                method,
            } => {
                let func_ty = self.statics.solution_of_node(func_node).unwrap();
                self.translate_iface_method_ap_helper(
                    st,
                    mono,
                    iface_def,
                    *method as u16,
                    &func_ty,
                );
            }
            Declaration::MemberFunction(f) => {
                let f_fully_qualified_name = &self.statics.fully_qualified_names[&f.name.id];
                self.translate_func_ap_helper(f, f_fully_qualified_name, func_node, mono, st);
            }
            Declaration::Struct(def) => {
                let mut nargs = 0;
                for field in &*def.fields {
                    // TODO: duplicated logic
                    let field_ty = field.ty.to_solved_type(&self.statics).unwrap().subst(mono);
                    if field_ty != SolvedType::Void {
                        nargs += 1;
                    }
                }
                self.emit(st, Instr::ConstructStruct(nargs));
            }
            Declaration::EnumVariant {
                e: enum_def,
                variant,
            } => {
                let nargs = match &enum_def.variants[*variant].data {
                    Some(data_ty) => {
                        let data_ty = data_ty.to_solved_type(&self.statics).unwrap().subst(mono);
                        match data_ty {
                            SolvedType::Tuple(elems) => {
                                // TODO: duplicated logic
                                let mut nargs = 0;
                                for elem in elems {
                                    if elem != SolvedType::Void {
                                        nargs += 1;
                                    }
                                }
                                nargs
                            }
                            SolvedType::Void => 0,
                            _ => 1,
                        }
                    }
                    None => 0,
                };
                if nargs > 1 {
                    self.emit(st, Instr::ConstructStruct(nargs));
                }

                if nargs == 0 {
                    self.emit(st, Instr::PushNil(1)); // TODO: optimize this away
                }

                self.emit(
                    st,
                    Instr::ConstructVariant {
                        tag: *variant as u16,
                    },
                );
            }
            Declaration::Intrinsic(b) => self.emit_intrinsic(st, mono, *b, func_node, false),
            Declaration::InterfaceOutputType { .. }
            | Declaration::InterfaceDef(_)
            | Declaration::Array
            | Declaration::Polytype(_)
            | Declaration::Enum { .. }
            | Declaration::Namespace(_)
            | Declaration::BuiltinType(_) => {
                unreachable!()
            }
        }
    }

    fn wrapper_header(&self, st: &mut TranslatorState, nargs: usize, for_function_body: bool) {
        if for_function_body {
            for i in (0..nargs as i16).rev() {
                self.emit(st, Instr::LoadOffset(-i - 1));
            }
        }
    }

    fn wrapper_footer(&self, st: &mut TranslatorState, nargs: usize, for_function_body: bool) {
        if for_function_body {
            if nargs == 0 {
                self.emit(st, Instr::ReturnVoid);
            } else {
                self.emit(st, Instr::Return(nargs as u32));
            }
        }
    }

    fn emit_intrinsic(
        &self,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
        b: IntrinsicOperation,
        func_node: AstNode,
        for_function_body: bool, // if emitting intrinsic for a function body, load arguments and return value
    ) {
        let nargs = match b {
            IntrinsicOperation::AddInt => 2,
            IntrinsicOperation::SubtractInt => 2,
            IntrinsicOperation::MultiplyInt => 2,
            IntrinsicOperation::DivideInt => 2,
            IntrinsicOperation::PowerInt => 2,
            IntrinsicOperation::Modulo => 2,
            IntrinsicOperation::AddFloat => 2,
            IntrinsicOperation::SubtractFloat => 2,
            IntrinsicOperation::MultiplyFloat => 2,
            IntrinsicOperation::DivideFloat => 2,
            IntrinsicOperation::PowerFloat => 2,
            IntrinsicOperation::Atan2 => 2,
            IntrinsicOperation::Ceil => 1,
            IntrinsicOperation::Floor => 1,
            IntrinsicOperation::Round => 1,
            IntrinsicOperation::Sqrt => 1,
            IntrinsicOperation::Sin => 1,
            IntrinsicOperation::Cos => 1,
            IntrinsicOperation::Tan => 1,
            IntrinsicOperation::Asin => 1,
            IntrinsicOperation::Acos => 1,
            IntrinsicOperation::Atan => 1,
            IntrinsicOperation::Log => 1,
            IntrinsicOperation::Log2 => 1,
            IntrinsicOperation::Log10 => 1,
            IntrinsicOperation::LessThanInt => 2,
            IntrinsicOperation::LessThanOrEqualInt => 2,
            IntrinsicOperation::GreaterThanInt => 2,
            IntrinsicOperation::GreaterThanOrEqualInt => 2,
            IntrinsicOperation::EqualInt => 2,
            IntrinsicOperation::LessThanFloat => 2,
            IntrinsicOperation::LessThanOrEqualFloat => 2,
            IntrinsicOperation::GreaterThanFloat => 2,
            IntrinsicOperation::GreaterThanOrEqualFloat => 2,
            IntrinsicOperation::EqualFloat => 2,
            IntrinsicOperation::EqualString => 2,
            IntrinsicOperation::IntToFloat => 1,
            IntrinsicOperation::FloatToInt => 1,
            IntrinsicOperation::IntToString => 1,
            IntrinsicOperation::FloatToString => 1,
            IntrinsicOperation::ConcatStrings => 2,
            IntrinsicOperation::ArrayPush => {
                // TODO: code duplication, see inlining of array.push()
                let Some(SolvedType::Function(args, _)) = self.get_ty(mono, func_node.clone())
                else {
                    unreachable!()
                };
                // second arg is element being pushed
                let arg_ty = &args[1];
                if *arg_ty == SolvedType::Void { 1 } else { 2 }
            }
            IntrinsicOperation::ArrayLength => 1,
            IntrinsicOperation::ArrayPop => 1,
            IntrinsicOperation::Panic => 1,
        };
        self.wrapper_header(st, nargs, for_function_body);
        match b {
            IntrinsicOperation::AddInt => {
                self.emit(st, Instr::AddInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::SubtractInt => {
                self.emit(st, Instr::SubInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::MultiplyInt => {
                self.emit(st, Instr::MulInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::DivideInt => {
                self.emit(st, Instr::DivInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::PowerInt => {
                self.emit(st, Instr::PowInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Modulo => {
                self.emit(st, Instr::Modulo(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::AddFloat => {
                self.emit(st, Instr::AddFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::SubtractFloat => {
                self.emit(st, Instr::SubFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::MultiplyFloat => {
                self.emit(st, Instr::MulFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::DivideFloat => {
                self.emit(st, Instr::DivFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::PowerFloat => {
                self.emit(st, Instr::PowFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Atan2 => {
                self.emit(st, Instr::Atan2(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Ceil => {
                self.emit(st, Instr::Ceil(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Floor => {
                self.emit(st, Instr::Floor(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Round => {
                self.emit(st, Instr::Round(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Sqrt => {
                self.emit(st, Instr::SquareRoot(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Sin => {
                self.emit(st, Instr::Sin(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Cos => {
                self.emit(st, Instr::Cos(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Tan => {
                self.emit(st, Instr::Tan(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Asin => {
                self.emit(st, Instr::Asin(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Acos => {
                self.emit(st, Instr::Acos(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Atan => {
                self.emit(st, Instr::Atan(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Log => {
                self.emit(st, Instr::Log(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Log2 => {
                self.emit(st, Instr::Log2(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::Log10 => {
                self.emit(st, Instr::Log10(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::LessThanInt => {
                self.emit(st, Instr::LessThanInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::LessThanOrEqualInt => {
                self.emit(st, Instr::LessThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::GreaterThanInt => {
                self.emit(st, Instr::GreaterThanInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::GreaterThanOrEqualInt => {
                self.emit(
                    st,
                    Instr::GreaterThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top),
                );
            }
            IntrinsicOperation::EqualInt => {
                self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::LessThanFloat => {
                self.emit(st, Instr::LessThanFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::LessThanOrEqualFloat => {
                self.emit(
                    st,
                    Instr::LessThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                );
            }
            IntrinsicOperation::GreaterThanFloat => {
                self.emit(st, Instr::GreaterThanFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::GreaterThanOrEqualFloat => {
                self.emit(
                    st,
                    Instr::GreaterThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                );
            }
            IntrinsicOperation::EqualFloat => {
                self.emit(st, Instr::EqualFloat(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::EqualString => {
                self.emit(st, Instr::EqualString(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::IntToFloat => {
                self.emit(st, Instr::IntToFloat(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::FloatToInt => {
                self.emit(st, Instr::FloatToInt(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::IntToString => {
                self.emit(st, Instr::IntToString(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::FloatToString => {
                self.emit(st, Instr::FloatToString(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::ConcatStrings => {
                self.emit(st, Instr::ConcatStrings(Reg::Top, Reg::Top, Reg::Top));
            }
            IntrinsicOperation::ArrayPush => {
                // TODO: code duplication, see inlining of array.push()
                let Some(SolvedType::Function(args, _)) = self.get_ty(mono, func_node.clone())
                else {
                    unreachable!()
                };
                // second arg is element being pushed
                let arg_ty = &args[1];
                if *arg_ty == SolvedType::Void {
                    self.emit(st, Instr::PushNil(1));
                }
                self.emit(st, Instr::ArrayPush(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::ArrayLength => {
                self.emit(st, Instr::ArrayLength(Reg::Top, Reg::Top));
            }
            IntrinsicOperation::ArrayPop => {
                // TODO: code duplication, see inlining of array.pop()
                self.emit(st, Instr::ArrayPop(Reg::Top, Reg::Top));
                let SolvedType::Function(_, ret_ty) = self.get_ty(mono, func_node.clone()).unwrap()
                else {
                    unreachable!()
                };
                if *ret_ty == SolvedType::Void {
                    self.emit(st, Instr::Pop);
                }
            }
            IntrinsicOperation::Panic => {
                self.emit(st, Instr::Panic);
            }
        }
        self.wrapper_footer(st, nargs, for_function_body);
    }

    fn emit_foreign(
        &self,
        st: &mut TranslatorState,
        func_decl: &Rc<FuncDecl>,
        libname: &PathBuf,
        symbol: &String,
        for_function_body: bool,
    ) {
        let args = self.calculate_args(&None, &func_decl.args, &MonomorphEnv::empty());
        let nargs = args.len();
        self.wrapper_header(st, nargs, for_function_body);
        // by this point we should know the name of the .so file that this external function should be located in

        // calling an external function just means
        // (1) loading the .so file (preferably do this when the VM starts up)
        // (2) locate the external function in this .so file by its symbol (preferably do this when VM starts up)
        // (3) invoke the function, which should have signature fn(&mut Vm) -> ()

        // the bytecode for calling the external function doesn't need to contain the .so name or the method name as a string.
        // it just needs to contain an idx into an array of foreign functions

        let lib_id = self.statics.dylibs.get_id(libname);

        let mut offset = 0;
        for i in 0..lib_id {
            offset += self.statics.dylib_to_funcs[&i].len();
        }

        let func_id = offset + self.statics.dylib_to_funcs[&lib_id].get_id(symbol) as usize;
        self.emit(st, Instr::CallExtern(func_id as u32));

        self.wrapper_footer(st, nargs, for_function_body);
    }

    fn emit_host(
        &self,
        st: &mut TranslatorState,
        func_decl: &Rc<FuncDecl>,
        for_function_body: bool,
    ) {
        let args = self.calculate_args(&None, &func_decl.args, &MonomorphEnv::empty());
        let nargs = args.len();
        self.wrapper_header(st, nargs, for_function_body);

        let idx = self.statics.host_funcs.get_id(func_decl) as u16;
        self.emit(st, Instr::HostFunc(idx));

        self.wrapper_footer(st, nargs, for_function_body);
    }

    // emit items for checking if a pattern matches the TOS, replacing it with a boolean
    fn translate_pat_comparison(
        &self,
        scrutinee_ty: &Type,
        pat: &Rc<Pat>,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
    ) {
        match &*pat.kind {
            PatKind::Wildcard | PatKind::Binding(_) | PatKind::Void => {
                let pat_ty = self.get_ty(mono, pat.node()).unwrap();

                if pat_ty != SolvedType::Void {
                    self.emit(st, Instr::Pop);
                }
                self.emit(st, Instr::PushBool(true));
                return;
            }
            _ => {}
        }

        match scrutinee_ty {
            Type::Int => match &*pat.kind {
                PatKind::Int(i) => {
                    self.emit(st, Instr::PushInt(*i));
                    self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top));
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::Float => match &*pat.kind {
                PatKind::Float(f) => {
                    self.emit(st, Instr::PushFloat(f.clone()));
                    self.emit(st, Instr::EqualFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::Bool => match &*pat.kind {
                PatKind::Bool(b) => {
                    self.emit(st, Instr::PushBool(*b));
                    self.emit(st, Instr::EqualBool(Reg::Top, Reg::Top, Reg::Top));
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::String => match &*pat.kind {
                PatKind::Str(s) => {
                    self.emit(st, Instr::PushString(s.clone()));
                    self.emit(st, Instr::EqualString(Reg::Top, Reg::Top, Reg::Top));
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::Nominal(_, _) => match &*pat.kind {
                PatKind::Variant(_prefixes, ctor, inner) => {
                    let Declaration::EnumVariant { variant, .. } =
                        &self.statics.resolution_map[&ctor.id]
                    else {
                        panic!("expected variable to be defined in node");
                    };
                    let tag_fail_label = make_label("tag_fail");
                    let end_label = make_label("endvariant");

                    self.emit(st, Instr::DeconstructVariant);
                    self.emit(st, Instr::PushInt(*variant as AbraInt));
                    self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top));
                    self.emit(st, Instr::JumpIfFalse(tag_fail_label.clone()));

                    let mut void_case = || {
                        self.emit(st, Instr::Pop);
                        self.emit(st, Instr::PushBool(true));
                        self.emit(st, Instr::Jump(end_label.clone()));
                    };
                    if let Some(inner) = inner {
                        let inner_ty = self.get_ty(mono, inner.node()).unwrap();
                        if inner_ty != SolvedType::Void {
                            self.translate_pat_comparison(&inner_ty, inner, st, mono);
                            self.emit(st, Instr::Jump(end_label.clone()));
                        } else {
                            void_case();
                        }
                    } else {
                        void_case();
                    }

                    // FAILURE
                    self.emit(st, Line::Label(tag_fail_label));
                    self.emit(st, Instr::Pop);

                    self.emit(st, Instr::PushBool(false));

                    self.emit(st, Line::Label(end_label));
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::Tuple(types) => match &*pat.kind {
                PatKind::Tuple(pats) => {
                    let final_element_success_label = make_label("tuple_success");
                    let end_label = make_label("endtuple");
                    // spill tuple elements onto stack
                    self.emit(st, Instr::DeconstructStruct);
                    // for each element of tuple pattern, compare to TOS
                    // if the comparison fails, pop all remaining tuple elements and jump to the next arm
                    // if it makes it through each tuple element, jump to the arm's expression
                    let failure_labels = (0..pats.len())
                        .map(|_| make_label("tuple_fail"))
                        .collect::<Vec<_>>();
                    for (i, pat) in pats.iter().enumerate() {
                        let ty = &types[i];
                        self.translate_pat_comparison(ty, pat, st, mono);
                        let is_last = i == pats.len() - 1;
                        self.emit(st, Instr::JumpIfFalse(failure_labels[i].clone()));
                        // SUCCESS
                        if is_last {
                            self.emit(st, Instr::Jump(final_element_success_label.clone()));
                        }
                    }
                    // SUCCESS CASE
                    self.emit(st, Line::Label(final_element_success_label));
                    self.emit(st, Instr::PushBool(true));
                    self.emit(st, Instr::Jump(end_label.clone()));

                    // FAILURE CASE
                    // clean up the remaining tuple elements before yielding false
                    self.emit(st, Line::Label(failure_labels[0].clone()));
                    for (i, label) in failure_labels[1..].iter().enumerate() {
                        if SolvedType::Void != types[i + 1] {
                            self.emit(st, Instr::Pop);
                        }
                        self.emit(st, Line::Label(label.clone()));
                    }
                    self.emit(st, Instr::PushBool(false));

                    self.emit(st, Line::Label(end_label));
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            SolvedType::Void => self.emit(st, Instr::PushBool(true)),
            SolvedType::Function(_, _) => {
                // functions are always not equal.
                self.emit(st, Instr::Pop);
                self.emit(st, Instr::PushBool(false));
            }
            SolvedType::Never => {
                // noop, will never execute
            }
            SolvedType::Poly(_) => unreachable!(),
            Type::InterfaceOutput(_) => unreachable!(),
        }
    }

    fn translate_stmt(
        &self,
        stmt: &Rc<Stmt>,
        is_last_in_block_expression: bool,
        offset_table: &OffsetTable,
        mono: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_current_file_and_lineno(st, stmt.node());
        match &*stmt.kind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr, offset_table, mono, st);
                self.handle_pat_binding(&pat.0, offset_table, st, mono);
            }
            StmtKind::Assign(expr1, assign_op, rvalue) => {
                let rvalue_ty = self.get_ty(mono, rvalue.node()).unwrap();
                match assign_op {
                    AssignOperator::Equal => {
                        if rvalue_ty != SolvedType::Void {
                            match &*expr1.kind {
                                // variable assignment
                                ExprKind::Variable(_) => {
                                    let Declaration::Var(node) =
                                        &self.statics.resolution_map[&expr1.id]
                                    else {
                                        panic!("expected variableto be defined in node");
                                    };
                                    let idx = offset_table.get(&node.id()).unwrap();
                                    self.translate_expr(rvalue, offset_table, mono, st);
                                    self.emit(st, Instr::StoreOffset(*idx));
                                }
                                // struct member assignment
                                ExprKind::MemberAccess(accessed, field_name) => {
                                    // TODO: if member function is being assigned to, that should be disallowed earlier by the compiler
                                    // for instance, Person.fullname = (p: Person) -> "hello world". Should not be allowed.
                                    self.translate_expr(rvalue, offset_table, mono, st);
                                    self.translate_expr(accessed, offset_table, mono, st);
                                    let idx = self.idx_of_field(
                                        &self.statics,
                                        mono,
                                        accessed,
                                        &field_name.v,
                                    );
                                    self.emit(st, Instr::SetField(idx, Reg::Top));
                                }
                                // array assignment
                                ExprKind::IndexAccess(array, index) => {
                                    self.translate_expr(rvalue, offset_table, mono, st);
                                    self.translate_expr(index, offset_table, mono, st);
                                    self.translate_expr(array, offset_table, mono, st);
                                    self.emit(st, Instr::SetIndex(Reg::Top, Reg::Top));
                                }
                                _ => unreachable!(),
                            }
                        }
                    }
                    AssignOperator::PlusEq => {
                        let add_instr = |st| {
                            match rvalue_ty {
                                SolvedType::Int => {
                                    self.emit(st, Instr::AddInt(Reg::Top, Reg::Top, Reg::Top));
                                }
                                SolvedType::Float => {
                                    self.emit(st, Instr::AddFloat(Reg::Top, Reg::Top, Reg::Top));
                                }
                                _ => unreachable!(),
                            };
                        };
                        match &*expr1.kind {
                            // variable assignment
                            ExprKind::Variable(_) => {
                                let Declaration::Var(node) =
                                    &self.statics.resolution_map[&expr1.id]
                                else {
                                    panic!("expected variableto be defined in node");
                                };
                                let idx = offset_table.get(&node.id()).unwrap();
                                // load x
                                self.emit(st, Instr::LoadOffset(*idx));
                                // add number
                                self.translate_expr(rvalue, offset_table, mono, st);
                                add_instr(st);
                                // store in x
                                self.emit(st, Instr::StoreOffset(*idx));
                            }
                            // struct member assignment
                            ExprKind::MemberAccess(accessed, field_name) => {
                                // load struct.field
                                self.translate_expr(accessed, offset_table, mono, st);
                                let idx =
                                    self.idx_of_field(&self.statics, mono, accessed, &field_name.v);
                                self.emit(st, Instr::GetField(idx, Reg::Top));
                                // add number
                                self.translate_expr(rvalue, offset_table, mono, st);
                                add_instr(st);
                                // store in struct.field
                                self.translate_expr(accessed, offset_table, mono, st);
                                let idx =
                                    self.idx_of_field(&self.statics, mono, accessed, &field_name.v);
                                self.emit(st, Instr::SetField(idx, Reg::Top));
                            }
                            // array assignment
                            ExprKind::IndexAccess(array, index) => {
                                // load from array at index
                                self.translate_expr(index, offset_table, mono, st);
                                self.translate_expr(array, offset_table, mono, st);
                                self.emit(st, Instr::GetIndex(Reg::Top, Reg::Top));
                                // add number
                                self.translate_expr(rvalue, offset_table, mono, st);
                                add_instr(st);
                                // store in array at index
                                self.translate_expr(index, offset_table, mono, st);
                                self.translate_expr(array, offset_table, mono, st);
                                self.emit(st, Instr::SetIndex(Reg::Top, Reg::Top));
                            }
                            // TODO: allow tuples on LHS of assignment
                            _ => unreachable!(),
                        }
                    }
                }
            }
            StmtKind::Expr(expr) => {
                let expr_ty = self.get_ty(mono, expr.node()).unwrap();
                let yields_value = expr_ty != SolvedType::Void && expr_ty != SolvedType::Never;
                self.translate_expr(expr, offset_table, mono, st);
                if !is_last_in_block_expression && yields_value {
                    self.emit(st, Instr::Pop);
                }
            }
            StmtKind::Break => {
                let enclosing_loop = st.loop_stack.last().unwrap();
                self.emit(st, Instr::Jump(enclosing_loop.end_label.clone()));
            }
            StmtKind::Continue => {
                let enclosing_loop = st.loop_stack.last().unwrap();
                self.emit(st, Instr::Jump(enclosing_loop.start_label.clone()));
            }
            StmtKind::Return(expr) => {
                self.translate_expr(expr, offset_table, mono, st);
                let ret_ty = self.get_ty(mono, expr.node()).unwrap();
                if ret_ty == SolvedType::Void {
                    self.emit(st, Instr::ReturnVoid);
                } else {
                    let return_nargs = st.return_stack.last().unwrap();
                    self.emit(st, Instr::Return(*return_nargs));
                }
            }
            StmtKind::WhileLoop(cond, statements) => {
                let start_label = make_label("while_start");
                let end_label = make_label("while_end");

                self.emit(st, Line::Label(start_label.clone()));
                self.translate_expr(cond, offset_table, mono, st);
                self.emit(st, Instr::JumpIfFalse(end_label.clone()));
                st.loop_stack.push(EnclosingLoop {
                    start_label: start_label.clone(),
                    end_label: end_label.clone(),
                });
                for statement in statements.iter() {
                    self.translate_stmt(statement, false, offset_table, mono, st);
                }
                st.loop_stack.pop();
                self.emit(st, Instr::Jump(start_label));
                self.emit(st, Line::Label(end_label));
            }
            StmtKind::ForLoop(pat, iterable, statements) => {
                self.translate_expr(iterable, offset_table, mono, st);
                // iterable.make_iterator()
                let Some(Declaration::InterfaceDef(iterable_iface_def)) = self
                    .statics
                    .root_namespace
                    .get_declaration("prelude.Iterable")
                else {
                    unreachable!()
                };
                let fn_make_iterator_ty = &self.statics.for_loop_make_iterator_types[&stmt.id];
                self.translate_iface_method_ap_helper(
                    st,
                    mono,
                    &iterable_iface_def,
                    0,
                    fn_make_iterator_ty,
                );
                // while loop:
                let start_label = make_label("for_start");
                let end_label_iter = make_label("for_end_iter");
                let end_label_break = make_label("for_end_break");
                self.emit(st, Line::Label(start_label.clone()));
                // iterator.next()
                self.emit(st, Instr::Duplicate);
                let Some(Declaration::InterfaceDef(iterator_iface_def)) = self
                    .statics
                    .root_namespace
                    .get_declaration("prelude.Iterator")
                else {
                    unreachable!()
                };
                let fn_next_ty = &self.statics.for_loop_next_types[&stmt.id];
                self.translate_iface_method_ap_helper(st, mono, &iterator_iface_def, 0, fn_next_ty);
                // check return value of iterator.next() and branch
                self.emit(st, Instr::DeconstructVariant);
                self.emit(st, Instr::PushInt(0 as AbraInt));
                self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top));
                self.emit(st, Instr::JumpIfFalse(end_label_iter.clone()));
                self.handle_pat_binding(pat, offset_table, st, mono);
                st.loop_stack.push(EnclosingLoop {
                    start_label: start_label.clone(),
                    end_label: end_label_break.clone(),
                });
                for statement in statements.iter() {
                    self.translate_stmt(statement, false, offset_table, mono, st);
                }
                st.loop_stack.pop();
                self.emit(st, Instr::Jump(start_label));
                self.emit(st, Line::Label(end_label_iter));
                self.emit(st, Instr::Pop);
                self.emit(st, Line::Label(end_label_break));
                self.emit(st, Instr::Pop);
            }
        }
    }

    fn handle_func_call(
        &self,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
        overload_ty: Option<Type>,
        func_name: &String,
        func_def: &Rc<FuncDef>,
    ) {
        if let Some(overload_ty) = &overload_ty {
            assert!(overload_ty.monotype().is_some());
        }
        let desc = FuncDesc {
            kind: FuncKind::NamedFunc(func_def.clone()),
            overload_ty: overload_ty.clone(),
        };
        let label = self.get_func_label(st, desc, func_name);
        let is_func = |ty: &Option<SolvedType>, arg: SolvedType, out: SolvedType| {
            *ty == Some(SolvedType::Function(vec![arg], out.into()))
        };
        let is_ident_func = |ty: &Option<SolvedType>, arg: SolvedType| {
            *ty == Some(SolvedType::Function(vec![arg.clone()], arg.into()))
        };
        let second_arg_is_void = |ty: &Option<SolvedType>| {
            if let Some(SolvedType::Function(args, _)) = ty {
                // second arg is element being pushed
                args[1] == SolvedType::Void
            } else {
                false
            }
        };
        let ret_is_void = |ty: &Option<SolvedType>| {
            if let Some(SolvedType::Function(_, ret)) = ty {
                **ret == SolvedType::Void
            } else {
                false
            }
        };
        match func_name.as_str() {
            // inline basic/fundamental operations instead of performing function call
            "array.push" => {
                // arrays of void use dummy values
                if second_arg_is_void(&overload_ty) {
                    self.emit(st, Instr::PushNil(1));
                }
                self.emit(st, Instr::ArrayPush(Reg::Top, Reg::Top))
            }
            "array.len" => self.emit(st, Instr::ArrayLength(Reg::Top, Reg::Top)),
            "array.pop" => {
                self.emit(st, Instr::ArrayPop(Reg::Top, Reg::Top));
                // arrays of void use dummy values
                if ret_is_void(&overload_ty) {
                    self.emit(st, Instr::Pop);
                }
            }
            "prelude.ToString.str"
                if is_func(&overload_ty, SolvedType::String, SolvedType::String) =>
            { /* noop */ }
            "prelude.ToString.str"
                if is_func(&overload_ty, SolvedType::Int, SolvedType::String) =>
            {
                self.emit(st, Instr::IntToString(Reg::Top, Reg::Top));
            }
            "prelude.ToString.str"
                if is_func(&overload_ty, SolvedType::Float, SolvedType::String) =>
            {
                self.emit(st, Instr::FloatToString(Reg::Top, Reg::Top));
            }
            "prelude.Clone.clone"
                if is_ident_func(&overload_ty, SolvedType::Int)
                    || is_ident_func(&overload_ty, SolvedType::Float)
                    || is_ident_func(&overload_ty, SolvedType::Bool)
                    || is_ident_func(&overload_ty, SolvedType::Void)
                    || is_ident_func(&overload_ty, SolvedType::String) =>
            { /* noop */ }
            _ => {
                let (args, _, _) = self.calculate_args_captures_locals(
                    &overload_ty,
                    &func_def.args,
                    &func_def.body,
                    mono,
                );
                let nargs = args.len();
                self.emit(st, Instr::Call(nargs, label));
            }
        }
    }

    fn get_func_label(
        &self,
        st: &mut TranslatorState,
        desc: FuncDesc,
        func_name: &String, // TODO: instead of passing in func_name just get it from the FuncDesc.
    ) -> Label {
        let entry = st.func_map.entry(desc.clone());
        match entry {
            std::collections::hash_map::Entry::Occupied(o) => o.get().clone(),
            std::collections::hash_map::Entry::Vacant(v) => {
                st.funcs_to_generate.push(desc.clone());
                let label = match &desc.overload_ty {
                    None => func_name.clone(),
                    Some(overload_ty) => {
                        let monoty = overload_ty.monotype().unwrap();
                        let mut label_hint = format!("{func_name}__{monoty}");
                        if let FuncKind::AnonymousFunc {
                            capture_types_concrete,
                            ..
                        } = desc.kind
                            && !capture_types_concrete.is_empty()
                        {
                            let label_hint = &mut label_hint;
                            swrite!(label_hint, "__");
                            for (i, ty) in capture_types_concrete.into_iter().enumerate() {
                                if i != 0 {
                                    swrite!(label_hint, "_");
                                }
                                swrite!(label_hint, "{ty}");
                            }
                        }
                        label_hint.retain(|c| !c.is_whitespace());
                        make_label(&label_hint)
                    }
                };
                v.insert(label.clone());
                label
            }
        }
    }

    fn handle_pat_binding(
        &self,
        pat: &Rc<Pat>,
        locals: &OffsetTable,
        st: &mut TranslatorState,
        mono: &MonomorphEnv,
    ) {
        match &*pat.kind {
            PatKind::Binding(_) => {
                let pat_ty = self.get_ty(mono, pat.node()).unwrap();

                if pat_ty != SolvedType::Void {
                    let idx = locals.get(&pat.id).unwrap();
                    self.emit(st, Instr::StoreOffset(*idx));
                }
            }
            PatKind::Tuple(pats) => {
                self.emit(st, Instr::DeconstructStruct);
                for pat in pats.iter() {
                    self.handle_pat_binding(pat, locals, st, mono);
                }
            }
            PatKind::Variant(_prefixes, _, inner) => {
                let mut void_case = || {
                    self.emit(st, Instr::Pop);
                };
                if let Some(inner) = inner {
                    let pat_ty = self.get_ty(mono, pat.node()).unwrap();

                    if pat_ty != SolvedType::Void {
                        // unpack tag and associated data
                        self.emit(st, Instr::DeconstructVariant);
                        // pop tag
                        self.emit(st, Instr::Pop);
                        self.handle_pat_binding(inner, locals, st, mono);
                    } else {
                        void_case();
                    }
                } else {
                    void_case();
                }
            }
            PatKind::Void => {
                // noop
            }
            PatKind::Bool(..)
            | PatKind::Int(..)
            | PatKind::Float(..)
            | PatKind::Str(..)
            | PatKind::Wildcard => {
                self.emit(st, Instr::Pop);
            }
        }
    }

    fn collect_locals_expr(&self, expr: &Expr, locals: &mut HashSet<AstNode>, mono: &MonomorphEnv) {
        match &*expr.kind {
            ExprKind::Block(statements) => {
                for statement in statements {
                    self.collect_locals_stmt(statement, locals, mono);
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    self.collect_locals_pat(&arm.pat, locals, mono);
                    self.collect_locals_stmt(&arm.stmt, locals, mono);
                }
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.collect_locals_expr(expr, locals, mono);
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.collect_locals_expr(expr, locals, mono);
                }
            }
            ExprKind::IfElse(cond, then_block, else_block) => {
                self.collect_locals_expr(cond, locals, mono);
                self.collect_locals_stmt(then_block, locals, mono);
                if let Some(else_block) = else_block {
                    self.collect_locals_stmt(else_block, locals, mono);
                }
            }
            ExprKind::BinOp(left, _, right) => {
                self.collect_locals_expr(left, locals, mono);
                self.collect_locals_expr(right, locals, mono);
            }
            ExprKind::Unop(_, right) => {
                self.collect_locals_expr(right, locals, mono);
            }
            ExprKind::MemberAccess(accessed, _) => {
                self.collect_locals_expr(accessed, locals, mono);
            }
            ExprKind::IndexAccess(array, index) => {
                self.collect_locals_expr(array, locals, mono);
                self.collect_locals_expr(index, locals, mono);
            }
            ExprKind::Unwrap(expr) => {
                self.collect_locals_expr(expr, locals, mono);
            }
            ExprKind::FuncAp(func, args) => {
                self.collect_locals_expr(func, locals, mono);
                for arg in args {
                    self.collect_locals_expr(arg, locals, mono);
                }
            }

            ExprKind::AnonymousFunction(..)
            | ExprKind::MemberAccessLeadingDot(..)
            | ExprKind::Variable(..)
            | ExprKind::Nil
            | ExprKind::Int(..)
            | ExprKind::Float(..)
            | ExprKind::Bool(..)
            | ExprKind::Str(..) => {}
        }
    }

    fn collect_locals_stmt(
        &self,
        statement: &Rc<Stmt>,
        locals: &mut HashSet<AstNode>,
        mono: &MonomorphEnv,
    ) {
        self.collect_locals_stmts(std::slice::from_ref(statement), locals, mono);
    }

    fn collect_locals_stmts(
        &self,
        statements: &[Rc<Stmt>],
        locals: &mut HashSet<AstNode>,
        mono: &MonomorphEnv,
    ) {
        for statement in statements {
            match &*statement.kind {
                StmtKind::Expr(expr) => {
                    self.collect_locals_expr(expr, locals, mono);
                }
                StmtKind::Let(_, pat, expr) => {
                    self.collect_locals_pat(&pat.0, locals, mono);
                    self.collect_locals_expr(expr, locals, mono);
                }
                StmtKind::Assign(_, _, expr) => {
                    self.collect_locals_expr(expr, locals, mono);
                }
                StmtKind::Continue | StmtKind::Break => {}
                StmtKind::Return(expr) => {
                    self.collect_locals_expr(expr, locals, mono);
                }
                StmtKind::WhileLoop(cond, statements) => {
                    self.collect_locals_expr(cond, locals, mono);
                    for statement in statements {
                        self.collect_locals_stmt(statement, locals, mono);
                    }
                }
                StmtKind::ForLoop(pat, iterable, statements) => {
                    self.collect_locals_pat(pat, locals, mono);
                    self.collect_locals_expr(iterable, locals, mono);
                    for statement in statements {
                        self.collect_locals_stmt(statement, locals, mono);
                    }
                }
            }
        }
    }

    fn collect_locals_pat(
        &self,
        pat: &Rc<Pat>,
        locals: &mut HashSet<AstNode>,
        mono: &MonomorphEnv,
    ) {
        match &*pat.kind {
            PatKind::Binding(_) => {
                let ty = self.get_ty(mono, pat.node()).unwrap();
                if ty != SolvedType::Void {
                    locals.insert(pat.node());
                }
            }
            PatKind::Tuple(pats) => {
                for pat in pats {
                    self.collect_locals_pat(pat, locals, mono);
                }
            }
            PatKind::Variant(_prefixes, _, Some(inner)) => {
                self.collect_locals_pat(inner, locals, mono);
            }
            PatKind::Variant(_prefixes, _, None) => {}
            PatKind::Void
            | PatKind::Bool(..)
            | PatKind::Int(..)
            | PatKind::Float(..)
            | PatKind::Str(..)
            | PatKind::Wildcard => {}
        }
    }

    // TODO: memoize this
    fn calculate_args_captures_locals(
        &self,
        overload_ty: &Option<SolvedType>,
        args: &[ArgMaybeAnnotated],
        body: &Rc<Expr>,
        mono: &MonomorphEnv,
    ) -> (Vec<AstNode>, HashSet<AstNode>, HashSet<AstNode>) {
        // TODO: this could be more performant. Lots of clones and a set difference()
        // TODO: use index map instead of HashSet?
        let mut locals = HashSet::default();
        self.collect_locals_expr(body, &mut locals, mono);
        let mut locals_and_args = locals.clone();
        let arg_ids = self.calculate_args(overload_ty, args, mono);

        locals_and_args.extend(arg_ids.clone());
        let mut captures = locals_and_args.clone();
        self.collect_captures_expr(body, &mut captures, mono);
        let captures: HashSet<_> = captures.difference(&locals_and_args).cloned().collect();
        (arg_ids, captures, locals)
    }

    fn calculate_args(
        &self,
        overload_ty: &Option<SolvedType>,
        args: &[ArgMaybeAnnotated],
        mono: &MonomorphEnv,
    ) -> Vec<AstNode> {
        let mut arg_ids = Vec::default();
        match overload_ty {
            Some(overload_ty) => {
                let SolvedType::Function(arg_tys, _) = overload_ty else { unreachable!() };
                for (i, arg_ty) in arg_tys.iter().enumerate().rev() {
                    if *arg_ty != SolvedType::Void {
                        arg_ids.push(args[i].0.node());
                    }
                }
            }
            None => {
                for (i, arg) in args.iter().enumerate().rev() {
                    let arg_ty = self.get_ty(mono, arg.0.node()).unwrap();
                    if arg_ty != SolvedType::Void {
                        arg_ids.push(args[i].0.node())
                    }
                }
            }
        }

        arg_ids
    }

    fn collect_captures_expr(
        &self,
        expr: &Rc<Expr>,
        captures: &mut HashSet<AstNode>,
        mono: &MonomorphEnv,
    ) {
        match &*expr.kind {
            ExprKind::Variable(_) => {
                // TODO: why Some(ty) ? All nodes should have a type, even if that type is Type or Namespace or something.
                if let Some(ty) = self.get_ty(mono, expr.node())
                    && ty != SolvedType::Void
                {
                    let decl = &self.statics.resolution_map[&expr.id];
                    if let Declaration::Var(node) = decl {
                        captures.insert(node.clone());
                    }
                }
            }
            ExprKind::Block(statements) => {
                for statement in statements {
                    self.collect_captures_stmt(statement, captures, mono);
                }
            }
            ExprKind::Match(_, arms) => {
                for arm in arms {
                    self.collect_captures_stmt(&arm.stmt, captures, mono);
                }
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.collect_captures_expr(expr, captures, mono);
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.collect_captures_expr(expr, captures, mono);
                }
            }
            ExprKind::IfElse(cond, then_block, else_block) => {
                self.collect_captures_expr(cond, captures, mono);
                self.collect_captures_stmt(then_block, captures, mono);
                if let Some(else_block) = else_block {
                    self.collect_captures_stmt(else_block, captures, mono);
                }
            }
            ExprKind::BinOp(left, _, right) => {
                self.collect_captures_expr(left, captures, mono);
                self.collect_captures_expr(right, captures, mono);
            }
            ExprKind::Unop(_, right) => {
                self.collect_captures_expr(right, captures, mono);
            }
            ExprKind::MemberAccess(accessed, _) => {
                self.collect_captures_expr(accessed, captures, mono);
            }
            ExprKind::IndexAccess(array, index) => {
                self.collect_captures_expr(array, captures, mono);
                self.collect_captures_expr(index, captures, mono);
            }
            ExprKind::Unwrap(expr) => {
                self.collect_captures_expr(expr, captures, mono);
            }
            ExprKind::FuncAp(func, args) => {
                self.collect_captures_expr(func, captures, mono);
                for arg in args {
                    self.collect_captures_expr(arg, captures, mono);
                }
            }
            ExprKind::AnonymousFunction(..)
            | ExprKind::MemberAccessLeadingDot(..)
            | ExprKind::Nil
            | ExprKind::Int(..)
            | ExprKind::Float(..)
            | ExprKind::Bool(..)
            | ExprKind::Str(..) => {}
        }
    }

    fn collect_captures_stmt(
        &self,
        statement: &Rc<Stmt>,
        locals: &mut HashSet<AstNode>,
        mono: &MonomorphEnv,
    ) {
        self.collect_captures_stmts(std::slice::from_ref(statement), locals, mono);
    }

    fn collect_captures_stmts(
        &self,
        statements: &[Rc<Stmt>],
        locals: &mut HashSet<AstNode>,
        mono: &MonomorphEnv,
    ) {
        for statement in statements {
            match &*statement.kind {
                StmtKind::Expr(expr) => {
                    self.collect_captures_expr(expr, locals, mono);
                }
                StmtKind::Let(_, _, expr) => {
                    self.collect_captures_expr(expr, locals, mono);
                }
                StmtKind::Assign(_, _, expr) => {
                    self.collect_captures_expr(expr, locals, mono);
                }
                StmtKind::Continue | StmtKind::Break => {}
                StmtKind::Return(expr) => {
                    self.collect_captures_expr(expr, locals, mono);
                }
                StmtKind::WhileLoop(cond, statements) => {
                    self.collect_captures_expr(cond, locals, mono);
                    for statement in statements {
                        self.collect_captures_stmt(statement, locals, mono);
                    }
                }
                StmtKind::ForLoop(_, iterable, statements) => {
                    self.collect_captures_expr(iterable, locals, mono);
                    for statement in statements {
                        self.collect_captures_stmt(statement, locals, mono);
                    }
                }
            }
        }
    }

    // TODO: this is O(N)
    // TODO: just precompute for all structs then lookup in table
    fn idx_of_field(
        &self,
        statics: &StaticsContext,
        mono: &MonomorphEnv,
        accessed: &Rc<Expr>,
        field_name: &str,
    ) -> u16 {
        let accessed_ty = self.get_ty(mono, accessed.node()).unwrap();

        match accessed_ty {
            Type::Nominal(Nominal::Struct(struct_def), _) => {
                let mut index = 0;
                // TODO duplicated logic
                for field in &*struct_def.fields {
                    if field.name.v == field_name {
                        return index as u16;
                    }
                    let field_ty = field.ty.to_solved_type(statics).unwrap();
                    if field_ty != SolvedType::Void {
                        index += 1;
                    }
                }
                panic!("could not find field")
            }
            _ => panic!("not a udt"),
        }
    }
}

fn make_label(hint: &str) -> Label {
    if hint.contains(" ") {
        panic!("Label hint cannot contain spaces");
    }
    static ID_COUNTER: AtomicUsize = AtomicUsize::new(1);
    let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{hint}__#{id:X}")
}

impl MonomorphEnv {
    fn update(&self, overloaded_ty: &Type, monomorphic_ty: &Type) {
        match (overloaded_ty, monomorphic_ty) {
            // recurse
            (Type::Function(args, out), Type::Function(args2, out2)) => {
                for i in 0..args.len() {
                    self.update(&args[i], &args2[i]);
                }
                self.update(out, out2);
            }
            (Type::Nominal(ident, params), Type::Nominal(ident2, params2)) => {
                assert_eq!(ident, ident2);
                for i in 0..params.len() {
                    self.update(&params[i], &params2[i]);
                }
            }
            (Type::Poly(polyty), _) => {
                self.extend(polyty.clone(), monomorphic_ty.clone());
            }
            (Type::Tuple(elems1), Type::Tuple(elems2)) => {
                for i in 0..elems1.len() {
                    self.update(&elems1[i], &elems2[i]);
                }
            }
            _ => {}
        }
    }
}

impl Type {
    fn subst(&self, monomorphic_env: &MonomorphEnv) -> Type {
        match self {
            Type::Function(args, out) => {
                let new_args = args.iter().map(|arg| arg.subst(monomorphic_env)).collect();
                let new_out = out.subst(monomorphic_env);
                Type::Function(new_args, Box::new(new_out))
            }
            Type::Nominal(ident, params) => {
                let new_params = params
                    .iter()
                    .map(|param| param.subst(monomorphic_env))
                    .collect();
                Type::Nominal(ident.clone(), new_params)
            }
            Type::Poly(polyty) => {
                if let Some(monomorphic_ty) = monomorphic_env.lookup(polyty) {
                    monomorphic_ty
                } else {
                    self.clone()
                }
            }
            Type::Tuple(elems) => {
                let new_elems = elems
                    .iter()
                    .map(|elem| elem.subst(monomorphic_env))
                    .collect();
                Type::Tuple(new_elems)
            }
            _ => self.clone(),
        }
    }
}
