/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::assembly::{Instr, Label, Line, LineVariant, Reg, remove_labels_and_constants};
use crate::ast::{ArgMaybeAnnotated, AstNode, BinaryOperator, FuncDef, InterfaceDef, ItemKind};
use crate::ast::{FileAst, FileDatabase, NodeId};
use crate::builtin::BuiltinOperation;
use crate::environment::Environment;
use crate::optimize_bytecode::optimize;
use crate::statics::Type;
use crate::statics::typecheck::Nominal;
use crate::statics::typecheck::SolvedType;
use crate::statics::{Declaration, PolytypeDeclaration, TypeProv};
use crate::vm::{AbraInt, Instr as VmInstr};
use crate::{
    ast::{Expr, ExprKind, Pat, PatKind, Stmt, StmtKind},
    statics::StaticsContext,
};
use std::mem;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
use utils::hash::HashMap;
use utils::hash::HashSet;
use utils::id_set::IdSet;

type OffsetTable = HashMap<NodeId, i16>;
type MonomorphEnv = Environment<PolytypeDeclaration, Type>;
pub(crate) type LabelMap = HashMap<Label, usize>;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
struct FuncDesc {
    kind: FuncKind,
    overload_ty: Option<SolvedType>,
}

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
enum FuncKind {
    NamedFunc(Rc<FuncDef>),
    AnonymousFunc(Rc<Expr>),
}

pub(crate) struct Translator {
    statics: StaticsContext,
    _files: FileDatabase,
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
    pub(crate) fn new(
        statics: StaticsContext,
        files: FileDatabase,
        file_asts: Vec<Rc<FileAst>>,
    ) -> Self {
        Self {
            statics,
            _files: files,
            file_asts,
        }
    }

    fn emit(&self, st: &mut TranslatorState, i: impl LineVariant) {
        let l: Line = i.to_line(self, st);

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

        let file = self._files.get(file_id).unwrap();
        let line_no = file.line_number_for_index(location.lo as usize);
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
        for file_data in self._files.files.iter() {
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

            let monomorph_env = MonomorphEnv::empty();

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
                collect_locals_stmt(&stmts, &mut locals);

                self.emit(st, Instr::PushNil(locals.len() as u16));
                let mut offset_table = OffsetTable::default();
                for (offset, node_id) in locals.iter().enumerate() {
                    offset_table.entry(*node_id).or_insert(offset as i16);
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
                    self.translate_stmt(
                        stmt,
                        i == statements.len() - 1,
                        &offset_table,
                        &monomorph_env,
                        st,
                    );
                }

                self.emit(st, Instr::Stop);
            }

            while !st.funcs_to_generate.is_empty() {
                // Generate bytecode for function bodies
                let mut iteration = Vec::new();
                mem::swap(&mut (iteration), &mut st.funcs_to_generate);
                for desc in iteration {
                    if let FuncKind::NamedFunc(f) = &desc.kind {
                        self.update_curr_function(st, &f.name.v);
                    }

                    let (func_ty, args, body) = match &desc.kind {
                        FuncKind::NamedFunc(f) => (
                            self.statics.solution_of_node(f.name.node()).unwrap(),
                            &f.args,
                            &f.body,
                        ),
                        FuncKind::AnonymousFunc(e) => {
                            let ExprKind::AnonymousFunction(args, _, body) = &*e.kind else {
                                unreachable!()
                            };
                            (self.statics.solution_of_node(e.node()).unwrap(), args, body)
                        }
                    };

                    let monomorph_env = MonomorphEnv::empty();
                    if let Some(overload_ty) = &desc.overload_ty {
                        monomorph_env.update(&func_ty, overload_ty);
                    }

                    let label = st.func_map.get(&desc).unwrap();
                    self.emit(st, Line::Label(label.clone()));

                    let mut locals = HashSet::default();
                    collect_locals_expr(body, &mut locals);
                    let locals_count = locals.len();
                    self.emit(st, Instr::PushNil(locals_count as u16));
                    let mut offset_table = OffsetTable::default();
                    for (i, arg) in args.iter().rev().enumerate() {
                        offset_table.entry(arg.0.id).or_insert(-(i as i16) - 1);
                    }
                    for (i, local) in locals.iter().enumerate() {
                        offset_table.entry(*local).or_insert(i as i16);
                    }
                    let nargs = count_args(&self.statics, args, desc.overload_ty);
                    st.return_stack.push(nargs as u32);
                    self.translate_expr(body, &offset_table, &monomorph_env, st);
                    st.return_stack.pop();

                    let SolvedType::Function(_, out_ty) = func_ty else { unreachable!() };
                    if *out_ty == SolvedType::Void {
                        self.emit(st, Instr::ReturnVoid);
                    } else {
                        self.emit(st, Instr::Return(nargs as u32));
                    }
                }
            }
        }

        // RUN OPTIMIZATIONS HERE

        st.lines = optimize(st.lines);

        st
    }

    fn translate_expr(
        &self,
        expr: &Rc<Expr>,
        offset_table: &OffsetTable,
        monomorph_env: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_current_file_and_lineno(st, expr.node());

        match &*expr.kind {
            ExprKind::Variable(_) => match &self.statics.resolution_map[&expr.id] {
                Declaration::EnumVariant { variant, .. } => {
                    self.emit(st, Instr::PushNil(1));
                    self.emit(
                        st,
                        Instr::ConstructVariant {
                            tag: *variant as u16,
                        },
                    );
                }
                Declaration::Var(node) => {
                    let expr_ty = self.statics.solution_of_node(expr.node()).unwrap();
                    let expr_ty = expr_ty.subst(monomorph_env);
                    if expr_ty != SolvedType::Void {
                        let idx = offset_table.get(&node.id()).unwrap();
                        self.emit(st, Instr::LoadOffset(*idx));
                    }
                }
                Declaration::Builtin(b) => match b {
                    BuiltinOperation::Newline => {
                        self.emit(st, Instr::PushString("\n".to_owned()));
                    }
                    _ => {
                        unimplemented!()
                    }
                },
                Declaration::InterfaceOutputType { .. } | Declaration::BuiltinType(_) => {
                    unreachable!()
                }
                Declaration::FreeFunction(f) => {
                    let name = &self.statics.fully_qualified_names[&f.name.id];
                    self.emit(
                        st,
                        Instr::MakeClosure {
                            func_addr: name.clone(),
                        },
                    );
                }

                Declaration::_ForeignFunction { .. }
                | Declaration::HostFunction(..)
                | Declaration::InterfaceMethod { .. }
                | Declaration::MemberFunction { .. } => unimplemented!(),

                Declaration::Struct(_)
                | Declaration::Enum { .. }
                | Declaration::InterfaceDef(_) => {
                    // noop, does not exist at runtime
                    //
                    // Person.fullname(my_person)
                    // ^^^^^
                    // Clone.clone(my_array)
                    // ^^^^^
                }

                Declaration::Array | Declaration::Polytype(_) => {
                    unreachable!()
                }
            },
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
            ExprKind::Void => {}
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
                self.translate_expr(left, offset_table, monomorph_env, st);
                match op {
                    BinaryOperator::Or => {
                        let short_circuit = make_label("short_circuit_or");
                        let end_label = make_label("end_or");
                        self.emit(st, Instr::JumpIf(short_circuit.clone()));
                        self.translate_expr(right, offset_table, monomorph_env, st);
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
                        self.translate_expr(right, offset_table, monomorph_env, st);
                        self.emit(st, Instr::Jump(end_label.clone()));
                        self.emit(st, short_circuit);
                        self.emit(st, Instr::PushBool(false));
                        self.emit(st, end_label);
                        return;
                    }
                    _ => {}
                };
                self.translate_expr(right, offset_table, monomorph_env, st);
                let mut helper = |monomorph_env: &MonomorphEnv, method_name: &str| {
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
                    let arg1_ty = self.statics.solution_of_node(left.node()).unwrap();
                    let arg2_ty = self.statics.solution_of_node(right.node()).unwrap();
                    let out_ty = self.statics.solution_of_node(expr.node()).unwrap();
                    let func_ty = Type::Function(vec![arg1_ty, arg2_ty], out_ty.into());

                    self.translate_iface_method_ap_helper(
                        st,
                        monomorph_env,
                        &iface_def,
                        method as u16,
                        &func_ty,
                    );
                };
                let arg1_ty = self.statics.solution_of_node(left.node()).unwrap();
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
                        _ => unreachable!(),
                    },
                    BinaryOperator::LessThan => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::LessThanInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::LessThanFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        _ => unreachable!(),
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
                        _ => unreachable!(),
                    },
                    BinaryOperator::LessThanOrEqual => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::LessThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => self.emit(
                            st,
                            Instr::LessThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                        ),
                        _ => unreachable!(),
                    },
                    BinaryOperator::Equal => match arg1_ty {
                        SolvedType::Int => {
                            self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Float => {
                            self.emit(st, Instr::EqualFloat(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::Bool => {
                            self.emit(st, Instr::EqualBool(Reg::Top, Reg::Top, Reg::Top))
                        }
                        SolvedType::String => self.emit(st, Instr::EqualString),
                        _ => {
                            helper(monomorph_env, "prelude.Equal.equal");
                        }
                    },
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
                        let Declaration::FreeFunction(func) = format_append_decl else {
                            unreachable!()
                        };
                        let func_name = &self.statics.fully_qualified_names[&func.name.id];

                        let arg2_ty = self.statics.solution_of_node(right.node()).unwrap();
                        let out_ty = self.statics.solution_of_node(expr.node()).unwrap();
                        let specific_func_ty =
                            Type::Function(vec![arg1_ty, arg2_ty], out_ty.into());

                        let substituted_ty = specific_func_ty.subst(monomorph_env);

                        self.handle_func_call(st, Some(substituted_ty), func_name, &func);
                    }
                    BinaryOperator::Or => unreachable!(),
                    BinaryOperator::And => unreachable!(),
                    BinaryOperator::Mod => {
                        self.emit(st, Instr::Modulo(Reg::Top, Reg::Top, Reg::Top))
                    }
                }
            }
            ExprKind::MemberFuncAp(expr, fname, args) => {
                if let Some(expr) = expr {
                    self.translate_expr(expr, offset_table, monomorph_env, st);
                }
                for arg in args {
                    self.translate_expr(arg, offset_table, monomorph_env, st);
                }

                let decl = &self.statics.resolution_map[&fname.id];
                self.translate_func_ap(decl, fname.node(), offset_table, monomorph_env, st);
            }
            ExprKind::FuncAp(func, args) => {
                for arg in args {
                    self.translate_expr(arg, offset_table, monomorph_env, st);
                }
                let decl = match &*func.kind {
                    ExprKind::Variable(_) => &self.statics.resolution_map[&func.id],
                    ExprKind::MemberAccess(_prefix, ident) => {
                        &self.statics.resolution_map[&ident.id]
                    }
                    ExprKind::MemberAccessLeadingDot(..) => unimplemented!(),

                    ExprKind::Void
                    | ExprKind::Int(_)
                    | ExprKind::Float(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Str(_)
                    | ExprKind::Array(_)
                    | ExprKind::BinOp(..)
                    | ExprKind::Tuple(..) => panic!("lhs of FuncAp not a function"),

                    // TODO: shouldn't these all just be treated like a function object?
                    ExprKind::MemberFuncAp(..) => unimplemented!(),
                    ExprKind::Unwrap(..) => unimplemented!(),
                    ExprKind::IfElse(_expr, _expr1, _expr2) => unimplemented!(),
                    ExprKind::Match(_expr, _match_armss) => unimplemented!(),
                    ExprKind::Block(_stmts) => unimplemented!(),
                    ExprKind::IndexAccess(_expr, _expr1) => unimplemented!(),
                    ExprKind::FuncAp(_expr, _exprs) => unimplemented!(),
                    ExprKind::AnonymousFunction(_items, _, _expr) => unimplemented!(),
                };

                self.translate_func_ap(decl, func.node(), offset_table, monomorph_env, st);
            }
            ExprKind::Block(statements) => {
                for (i, statement) in statements.iter().enumerate() {
                    self.translate_stmt(
                        statement,
                        i == statements.len() - 1,
                        offset_table,
                        monomorph_env,
                        st,
                    );
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr, offset_table, monomorph_env, st);
                }
                let mut nargs = 0;
                for expr in exprs {
                    // TODO: duplicated logic
                    let expr_ty = self
                        .statics
                        .solution_of_node(expr.node())
                        .unwrap()
                        .subst(monomorph_env);
                    if expr_ty != SolvedType::Void {
                        nargs += 1;
                    }
                }
                self.emit(st, Instr::ConstructStruct(nargs));
            }
            ExprKind::IfElse(cond, then_block, else_block) => {
                self.translate_expr(cond, offset_table, monomorph_env, st);
                let else_label = make_label("else");
                let end_label = make_label("endif");
                self.emit(st, Instr::JumpIfFalse(else_label.clone()));
                self.translate_expr(then_block, offset_table, monomorph_env, st);
                self.emit(st, Instr::Jump(end_label.clone()));
                self.emit(st, Line::Label(else_label));
                self.translate_expr(else_block, offset_table, monomorph_env, st);
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
                } else {
                    let expr_ty = self
                        .statics
                        .solution_of_node(expr.node())
                        .unwrap()
                        .subst(monomorph_env);
                    if expr_ty != SolvedType::Void {
                        self.translate_expr(accessed, offset_table, monomorph_env, st);
                        let idx =
                            idx_of_field(&self.statics, monomorph_env, accessed, &field_name.v);
                        self.emit(st, Instr::GetField(idx, Reg::Top));
                    }
                }
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr, offset_table, monomorph_env, st);
                }
                self.emit(st, Instr::ConstructArray(exprs.len() as u32));
            }
            ExprKind::IndexAccess(array, index) => {
                self.translate_expr(index, offset_table, monomorph_env, st);
                self.translate_expr(array, offset_table, monomorph_env, st);
                self.emit(st, Instr::GetIdx(Reg::Top, Reg::Top));
            }
            ExprKind::Match(expr, arms) => {
                let ty = self.statics.solution_of_node(expr.node()).unwrap();

                self.translate_expr(expr, offset_table, monomorph_env, st);
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
                    self.translate_pat_comparison(&ty, &arm.pat, st, monomorph_env);
                    self.emit(st, Instr::JumpIf(arm_label));
                }
                for (i, arm) in arms.iter().enumerate() {
                    self.emit(st, Line::Label(arm_labels[i].clone()));

                    self.handle_pat_binding(&arm.pat, offset_table, st, monomorph_env);

                    self.translate_stmt(&arm.stmt, true, offset_table, monomorph_env, st);
                    if i != arms.len() - 1 {
                        self.emit(st, Instr::Jump(end_label.clone()));
                    }
                }
                self.emit(st, Line::Label(end_label));
            }
            ExprKind::AnonymousFunction(..) => {
                let func_ty = self.statics.solution_of_node(expr.node()).unwrap();
                let overload_ty = if !func_ty.is_overloaded() {
                    None
                } else {
                    let substituted_ty = func_ty.subst(monomorph_env);
                    Some(substituted_ty)
                };

                let func_name = "lambda".to_string();
                let desc = FuncDesc {
                    kind: FuncKind::AnonymousFunc(expr.clone()),
                    overload_ty: overload_ty.clone(),
                };

                let label = self.get_func_label(st, desc, overload_ty, &func_name);

                self.emit(st, Instr::MakeClosure { func_addr: label });
            }
            ExprKind::Unwrap(expr) => {
                self.translate_expr(expr, offset_table, monomorph_env, st);

                let decl @ Declaration::FreeFunction(f) = &self
                    .statics
                    .root_namespace
                    .get_declaration("prelude.unwrap")
                    .unwrap()
                else {
                    panic!();
                };
                self.translate_func_ap(decl, f.name.node(), offset_table, monomorph_env, st);
            }
        }
    }

    // used for free functions and member functions
    fn translate_func_ap_helper(
        &self,
        f: &Rc<FuncDef>,
        f_fully_qualified_name: &String,
        func_node: AstNode,
        monomorph_env: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
        if !func_ty.is_overloaded() {
            self.handle_func_call(st, None, f_fully_qualified_name, f);
        } else {
            let specific_func_ty = self.statics.solution_of_node(func_node).unwrap();
            let substituted_ty = specific_func_ty.subst(monomorph_env);
            self.handle_func_call(st, Some(substituted_ty), f_fully_qualified_name, f);
        }
    }

    // used for interface methods
    fn translate_iface_method_ap_helper(
        &self,
        st: &mut TranslatorState,
        monomorph_env: &MonomorphEnv,
        iface_def: &Rc<InterfaceDef>,
        method: u16,
        func_ty: &SolvedType,
    ) {
        let substituted_ty = func_ty.subst(monomorph_env);
        let method = &iface_def.methods[method as usize].name;
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
                            Some(substituted_ty.clone()),
                            fully_qualified_name,
                            f,
                        );
                    }
                }
            }
        }
    }

    fn translate_func_ap(
        &self,
        decl: &Declaration,
        func_node: AstNode,
        offset_table: &OffsetTable,
        monomorph_env: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        match decl {
            Declaration::Var(node) => {
                let Some(SolvedType::Function(args, _)) =
                    self.statics.solution_of_node(node.clone())
                else {
                    unreachable!()
                };
                // assume it's a function object
                let idx = offset_table.get(&node.id()).unwrap();
                self.emit(st, Instr::LoadOffset(*idx));
                let nargs = args
                    .iter()
                    .map(|arg| arg.subst(monomorph_env))
                    .filter(|arg| *arg != SolvedType::Void)
                    .count();
                self.emit(st, Instr::CallFuncObj(nargs as u32));
            }
            Declaration::FreeFunction(f) => {
                let f_fully_qualified_name = &self.statics.fully_qualified_names[&f.name.id];
                self.translate_func_ap_helper(
                    f,
                    f_fully_qualified_name,
                    func_node,
                    monomorph_env,
                    st,
                );
            }
            Declaration::HostFunction(decl) => {
                let idx = self.statics.host_funcs.get_id(decl) as u16;
                self.emit(st, Instr::HostFunc(idx));
            }
            Declaration::_ForeignFunction {
                f: _decl,
                libname,
                symbol,
            } => {
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
            }
            Declaration::InterfaceMethod {
                iface: iface_def,
                method,
            } => {
                let func_ty = self.statics.solution_of_node(func_node).unwrap();
                self.translate_iface_method_ap_helper(
                    st,
                    monomorph_env,
                    iface_def,
                    *method as u16,
                    &func_ty,
                );
            }
            Declaration::MemberFunction { f } => {
                let f_fully_qualified_name = &self.statics.fully_qualified_names[&f.name.id];
                self.translate_func_ap_helper(
                    f,
                    f_fully_qualified_name,
                    func_node,
                    monomorph_env,
                    st,
                );
            }
            Declaration::Struct(def) => {
                let mut nargs = 0;
                for field in &*def.fields {
                    // TODO: duplicated logic
                    let field_ty = field
                        .ty
                        .to_solved_type(&self.statics)
                        .unwrap()
                        .subst(monomorph_env);
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
                        let data_ty = data_ty
                            .to_solved_type(&self.statics)
                            .unwrap()
                            .subst(monomorph_env);
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

                self.emit(
                    st,
                    Instr::ConstructVariant {
                        tag: *variant as u16,
                    },
                );
            }
            Declaration::Enum { .. } => {
                panic!("can't call enum name as ctor");
            }
            Declaration::Builtin(b) => match b {
                BuiltinOperation::AddInt => {
                    self.emit(st, Instr::AddInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::SubtractInt => {
                    self.emit(st, Instr::SubInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::MultiplyInt => {
                    self.emit(st, Instr::MulInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::DivideInt => {
                    self.emit(st, Instr::DivInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::PowerInt => {
                    self.emit(st, Instr::PowInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::Modulo => {
                    self.emit(st, Instr::Modulo(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::SqrtInt => {
                    self.emit(st, Instr::SquareRoot(Reg::Top, Reg::Top));
                }
                BuiltinOperation::AddFloat => {
                    self.emit(st, Instr::AddFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::SubtractFloat => {
                    self.emit(st, Instr::SubFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::MultiplyFloat => {
                    self.emit(st, Instr::MulFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::DivideFloat => {
                    self.emit(st, Instr::DivFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::PowerFloat => {
                    self.emit(st, Instr::PowFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::SqrtFloat => {
                    self.emit(st, Instr::SquareRoot(Reg::Top, Reg::Top));
                }
                BuiltinOperation::LessThanInt => {
                    self.emit(st, Instr::LessThanInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::LessThanOrEqualInt => {
                    self.emit(st, Instr::LessThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::GreaterThanInt => {
                    self.emit(st, Instr::GreaterThanInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::GreaterThanOrEqualInt => {
                    self.emit(
                        st,
                        Instr::GreaterThanOrEqualInt(Reg::Top, Reg::Top, Reg::Top),
                    );
                }
                BuiltinOperation::EqualInt => {
                    self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::LessThanFloat => {
                    self.emit(st, Instr::LessThanFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::LessThanOrEqualFloat => {
                    self.emit(
                        st,
                        Instr::LessThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                    );
                }
                BuiltinOperation::GreaterThanFloat => {
                    self.emit(st, Instr::GreaterThanFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::GreaterThanOrEqualFloat => {
                    self.emit(
                        st,
                        Instr::GreaterThanOrEqualFloat(Reg::Top, Reg::Top, Reg::Top),
                    );
                }
                BuiltinOperation::Not => {
                    self.emit(st, Instr::Not);
                }
                BuiltinOperation::EqualFloat => {
                    self.emit(st, Instr::EqualFloat(Reg::Top, Reg::Top, Reg::Top));
                }
                BuiltinOperation::EqualString => {
                    self.emit(st, Instr::EqualString);
                }
                BuiltinOperation::IntToFloat => {
                    self.emit(st, Instr::IntToFloat);
                }
                BuiltinOperation::FloatToInt => {
                    self.emit(st, Instr::FloatToInt);
                }
                BuiltinOperation::IntToString => {
                    self.emit(st, Instr::IntToString);
                }
                BuiltinOperation::FloatToString => {
                    self.emit(st, Instr::FloatToString);
                }
                BuiltinOperation::ConcatStrings => {
                    self.emit(st, Instr::ConcatStrings);
                }
                BuiltinOperation::ArrayPush => {
                    self.emit(st, Instr::ArrayPush(Reg::Top, Reg::Top));
                }
                BuiltinOperation::ArrayLength => {
                    self.emit(st, Instr::ArrayLength(Reg::Top, Reg::Top));
                }
                BuiltinOperation::ArrayPop => {
                    self.emit(st, Instr::ArrayPop(Reg::Top, Reg::Top));
                }
                BuiltinOperation::Panic => {
                    self.emit(st, Instr::Panic);
                }
                BuiltinOperation::Newline => {
                    panic!("not a function");
                }
            },
            Declaration::InterfaceOutputType { .. }
            | Declaration::InterfaceDef(_)
            | Declaration::Array
            | Declaration::Polytype(_)
            | Declaration::BuiltinType(_) => {
                unreachable!()
            }
        }
    }

    // emit items for checking if a pattern matches the TOS, replacing it with a boolean
    fn translate_pat_comparison(
        &self,
        scrutinee_ty: &Type,
        pat: &Rc<Pat>,
        st: &mut TranslatorState,
        monomorph_env: &MonomorphEnv,
    ) {
        match &*pat.kind {
            PatKind::Wildcard | PatKind::Binding(_) | PatKind::Void => {
                let pat_ty = self.statics.solution_of_node(pat.node()).unwrap();
                let pat_ty = pat_ty.subst(monomorph_env);

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
                    self.emit(st, Instr::EqualString);
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

                    if let Some(inner) = inner {
                        let inner_ty = self.statics.solution_of_node(inner.node()).unwrap();
                        self.translate_pat_comparison(&inner_ty, inner, st, monomorph_env);
                        self.emit(st, Instr::Jump(end_label.clone()));
                    } else {
                        self.emit(st, Instr::Pop);
                        self.emit(st, Instr::PushBool(true));
                        self.emit(st, Instr::Jump(end_label.clone()));
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
                        self.translate_pat_comparison(ty, pat, st, monomorph_env);
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
            _ => unimplemented!(),
        }
    }

    fn translate_stmt(
        &self,
        stmt: &Rc<Stmt>,
        is_last_in_block_expression: bool,
        offset_table: &OffsetTable,
        monomorph_env: &MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_current_file_and_lineno(st, stmt.node());
        match &*stmt.kind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr, offset_table, monomorph_env, st);
                self.handle_pat_binding(&pat.0, offset_table, st, monomorph_env);
            }
            StmtKind::Set(expr1, rvalue) => {
                let rvalue_ty = self
                    .statics
                    .solution_of_node(rvalue.node())
                    .unwrap()
                    .subst(monomorph_env);
                if rvalue_ty != SolvedType::Void {
                    match &*expr1.kind {
                        // variable assignment
                        ExprKind::Variable(_) => {
                            let Declaration::Var(node) = &self.statics.resolution_map[&expr1.id]
                            else {
                                panic!("expected variableto be defined in node");
                            };
                            let idx = offset_table.get(&node.id()).unwrap();
                            self.translate_expr(rvalue, offset_table, monomorph_env, st);
                            self.emit(st, Instr::StoreOffset(*idx));
                        }
                        // struct member assignment
                        ExprKind::MemberAccess(accessed, field_name) => {
                            self.translate_expr(rvalue, offset_table, monomorph_env, st);
                            self.translate_expr(accessed, offset_table, monomorph_env, st);
                            let idx =
                                idx_of_field(&self.statics, monomorph_env, accessed, &field_name.v);
                            self.emit(st, Instr::SetField(idx, Reg::Top));
                        }
                        // array assignment
                        ExprKind::IndexAccess(array, index) => {
                            self.translate_expr(rvalue, offset_table, monomorph_env, st);
                            self.translate_expr(index, offset_table, monomorph_env, st);
                            self.translate_expr(array, offset_table, monomorph_env, st);
                            self.emit(st, Instr::SetIdx(Reg::Top, Reg::Top));
                        }
                        _ => unimplemented!(),
                    }
                }
            }
            StmtKind::Expr(expr) => {
                // let ret_ty = match &*expr.kind {
                //     ExprKind::FuncAp(func_expr, _) => {
                //         // _print_node(&self.statics, func_expr.node());
                //         Some(self.statics.solution_of_node(expr.node()).unwrap())
                //     }
                //     ExprKind::MemberFuncAp(_, func_ident, _) => {
                //         // self.statics.resolution_map[func_ident]
                //         Some(self.statics.solution_of_node(expr.node()).unwrap())
                //     }
                //     _ => None,
                // };
                // let ret_ty = match func_ty {
                //     Some(func_ty) => {
                //         let SolvedType::Function(_, ret_ty) = func_ty else { unreachable!() };
                //         Some(*ret_ty)
                //     }
                //     None => None
                // };
                // let void_func_call = ret_ty == Some(SolvedType::Void);
                // _print_node(&self.statics, expr.node());
                let expr_ty = self
                    .statics
                    .solution_of_node(expr.node())
                    .unwrap()
                    .subst(monomorph_env);
                let is_void = expr_ty == SolvedType::Void;
                self.translate_expr(expr, offset_table, monomorph_env, st);
                if !is_last_in_block_expression && !is_void {
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
                self.translate_expr(expr, offset_table, monomorph_env, st);
                let ret_ty = self.statics.solution_of_node(expr.node()).unwrap();
                if ret_ty == SolvedType::Void {
                    self.emit(st, Instr::ReturnVoid);
                } else {
                    let return_nargs = st.return_stack.last().unwrap();
                    self.emit(st, Instr::Return(*return_nargs));
                }
            }
            StmtKind::If(cond, statements) => {
                self.translate_expr(cond, offset_table, monomorph_env, st);
                let end_label = make_label("endif");
                self.emit(st, Instr::JumpIfFalse(end_label.clone()));
                for statement in statements.iter() {
                    self.translate_stmt(statement, false, offset_table, monomorph_env, st);
                }
                self.emit(st, Line::Label(end_label));
            }
            StmtKind::WhileLoop(cond, statements) => {
                let start_label = make_label("while_start");
                let end_label = make_label("while_end");

                self.emit(st, Line::Label(start_label.clone()));
                self.translate_expr(cond, offset_table, monomorph_env, st);
                self.emit(st, Instr::JumpIfFalse(end_label.clone()));
                st.loop_stack.push(EnclosingLoop {
                    start_label: start_label.clone(),
                    end_label: end_label.clone(),
                });
                for statement in statements.iter() {
                    self.translate_stmt(statement, false, offset_table, monomorph_env, st);
                }
                st.loop_stack.pop();
                self.emit(st, Instr::Jump(start_label));
                self.emit(st, Line::Label(end_label));
            }
            StmtKind::ForLoop(pat, iterable, statements) => {
                self.translate_expr(iterable, offset_table, monomorph_env, st);
                // iterable.make_iterator()
                let Some(Declaration::InterfaceDef(iterable_iface_def)) = self
                    .statics
                    .root_namespace
                    .get_declaration("prelude.Iterable")
                else {
                    unreachable!()
                };
                let fn_make_iterator_ty = &self.statics.for_loop_make_iterator_types[&stmt.id];
                // println!("iterable_ty: {}", iterable_ty);
                // println!("fn_make_iterator_ty: {}", fn_make_iterator_ty);
                self.translate_iface_method_ap_helper(
                    st,
                    monomorph_env,
                    &iterable_iface_def,
                    0,
                    fn_make_iterator_ty,
                );
                // while loop:
                let start_label = make_label("for_start");
                let end_label = make_label("for_end");
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
                self.translate_iface_method_ap_helper(
                    st,
                    monomorph_env,
                    &iterator_iface_def,
                    0,
                    fn_next_ty,
                );
                // check return value of iterator.next() and branch
                self.emit(st, Instr::DeconstructVariant);
                self.emit(st, Instr::PushInt(0 as AbraInt));
                self.emit(st, Instr::EqualInt(Reg::Top, Reg::Top, Reg::Top));
                self.emit(st, Instr::JumpIfFalse(end_label.clone()));
                self.handle_pat_binding(pat, offset_table, st, monomorph_env);
                st.loop_stack.push(EnclosingLoop {
                    start_label: start_label.clone(),
                    end_label: end_label.clone(),
                });
                for statement in statements.iter() {
                    self.translate_stmt(statement, false, offset_table, monomorph_env, st);
                }
                st.loop_stack.pop();
                self.emit(st, Instr::Jump(start_label));
                self.emit(st, Line::Label(end_label));
                self.emit(st, Instr::Pop);
                self.emit(st, Instr::Pop);
            }
        }
    }

    fn handle_func_call(
        &self,
        st: &mut TranslatorState,
        overload_ty: Option<Type>,
        func_name: &String,
        func_def: &Rc<FuncDef>,
    ) {
        let desc = FuncDesc {
            kind: FuncKind::NamedFunc(func_def.clone()),
            overload_ty: overload_ty.clone(),
        };
        let label = self.get_func_label(st, desc, overload_ty.clone(), func_name);
        let is_func = |ty: &Option<SolvedType>, arg: SolvedType, out: SolvedType| {
            *ty == Some(SolvedType::Function(vec![arg], out.into()))
        };
        let is_ident_func = |ty: &Option<SolvedType>, arg: SolvedType| {
            *ty == Some(SolvedType::Function(vec![arg.clone()], arg.into()))
        };
        match (func_name.as_str(), overload_ty) {
            // inline basic/fundamental operations instead of performing function call
            ("array.push", _) => self.emit(st, Instr::ArrayPush(Reg::Top, Reg::Top)),
            ("array.len", _) => self.emit(st, Instr::ArrayLength(Reg::Top, Reg::Top)),
            ("array.pop", _) => self.emit(st, Instr::ArrayPop(Reg::Top, Reg::Top)),
            ("prelude.ToString.str", ty)
                if is_func(&ty, SolvedType::String, SolvedType::String) =>
            { /* noop */ }
            ("prelude.ToString.str", ty) if is_func(&ty, SolvedType::Int, SolvedType::String) => {
                self.emit(st, Instr::IntToString);
            }
            ("prelude.ToString.str", ty) if is_func(&ty, SolvedType::Float, SolvedType::String) => {
                self.emit(st, Instr::FloatToString);
            }
            ("prelude.Clone.clone", ty)
                if is_ident_func(&ty, SolvedType::Int)
                    || is_ident_func(&ty, SolvedType::Float)
                    || is_ident_func(&ty, SolvedType::Bool)
                    || is_ident_func(&ty, SolvedType::Void)
                    || is_ident_func(&ty, SolvedType::String) =>
            { /* noop */ }
            (_, overload_ty) => {
                let nargs = count_args(&self.statics, &func_def.args, overload_ty);
                self.emit(st, Instr::Call(nargs, label));
            }
        }
    }

    fn get_func_label(
        &self,
        st: &mut TranslatorState,
        desc: FuncDesc,
        overload_ty: Option<Type>,
        func_name: &String,
    ) -> Label {
        let entry = st.func_map.entry(desc.clone());
        match entry {
            std::collections::hash_map::Entry::Occupied(o) => o.get().clone(),
            std::collections::hash_map::Entry::Vacant(v) => {
                st.funcs_to_generate.push(desc);
                let label = match overload_ty {
                    None => func_name.clone(),
                    Some(overload_ty) => {
                        // println!("overload_ty {}, name {}", overload_ty, func_name);
                        let monoty = overload_ty.monotype().unwrap();
                        let mut label_hint = format!("{func_name}__{monoty}");
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
        monomorph_env: &MonomorphEnv,
    ) {
        match &*pat.kind {
            PatKind::Binding(_) => {
                let pat_ty = self.statics.solution_of_node(pat.node()).unwrap();
                let pat_ty = pat_ty.subst(monomorph_env);

                if pat_ty != SolvedType::Void {
                    let idx = locals.get(&pat.id).unwrap();
                    self.emit(st, Instr::StoreOffset(*idx));
                }
            }
            PatKind::Tuple(pats) => {
                self.emit(st, Instr::DeconstructStruct);
                for pat in pats.iter() {
                    self.handle_pat_binding(pat, locals, st, monomorph_env);
                }
            }
            PatKind::Variant(_prefixes, _, inner) => {
                if let Some(inner) = inner {
                    // unpack tag and associated data
                    self.emit(st, Instr::DeconstructVariant);
                    // pop tag
                    self.emit(st, Instr::Pop);
                    self.handle_pat_binding(inner, locals, st, monomorph_env);
                } else {
                    self.emit(st, Instr::Pop);
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
}

fn collect_locals_expr(expr: &Expr, locals: &mut HashSet<NodeId>) {
    match &*expr.kind {
        ExprKind::Block(statements) => {
            for statement in statements {
                collect_locals_stmt(std::slice::from_ref(statement), locals);
            }
        }
        ExprKind::Match(_, arms) => {
            for arm in arms {
                collect_locals_pat(&arm.pat, locals);
                collect_locals_stmt(std::slice::from_ref(&arm.stmt), locals);
            }
        }
        ExprKind::Array(exprs) => {
            for expr in exprs {
                collect_locals_expr(expr, locals);
            }
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs {
                collect_locals_expr(expr, locals);
            }
        }
        ExprKind::IfElse(cond, then_block, else_block) => {
            collect_locals_expr(cond, locals);
            collect_locals_expr(then_block, locals);
            collect_locals_expr(else_block, locals);
        }
        ExprKind::BinOp(left, _, right) => {
            collect_locals_expr(left, locals);
            collect_locals_expr(right, locals);
        }
        ExprKind::MemberAccess(accessed, _) => {
            collect_locals_expr(accessed, locals);
        }
        ExprKind::IndexAccess(array, index) => {
            collect_locals_expr(array, locals);
            collect_locals_expr(index, locals);
        }
        ExprKind::Unwrap(expr) => {
            collect_locals_expr(expr, locals);
        }
        ExprKind::FuncAp(func, args) => {
            collect_locals_expr(func, locals);
            for arg in args {
                collect_locals_expr(arg, locals);
            }
        }
        ExprKind::MemberFuncAp(expr, _, args) => {
            if let Some(expr) = expr {
                collect_locals_expr(expr, locals);
            }
            for arg in args {
                collect_locals_expr(arg, locals);
            }
        }
        ExprKind::AnonymousFunction(..)
        | ExprKind::MemberAccessLeadingDot(..)
        | ExprKind::Variable(..)
        | ExprKind::Void
        | ExprKind::Int(..)
        | ExprKind::Float(..)
        | ExprKind::Bool(..)
        | ExprKind::Str(..) => {}
    }
}

fn collect_locals_stmt(statements: &[Rc<Stmt>], locals: &mut HashSet<NodeId>) {
    for statement in statements {
        match &*statement.kind {
            StmtKind::Expr(expr) => {
                collect_locals_expr(expr, locals);
            }
            StmtKind::Let(_, pat, expr) => {
                collect_locals_pat(&pat.0, locals);
                collect_locals_expr(expr, locals);
            }
            StmtKind::Set(_, expr) => {
                collect_locals_expr(expr, locals);
            }
            StmtKind::Continue | StmtKind::Break => {}
            StmtKind::Return(expr) => {
                collect_locals_expr(expr, locals);
            }
            StmtKind::If(cond, body_statements) => {
                collect_locals_expr(cond, locals);
                for body_statement in body_statements {
                    collect_locals_stmt(std::slice::from_ref(body_statement), locals);
                }
            }
            StmtKind::WhileLoop(cond, statements) => {
                collect_locals_expr(cond, locals);
                for statement in statements {
                    collect_locals_stmt(std::slice::from_ref(statement), locals);
                }
            }
            StmtKind::ForLoop(pat, iterable, statements) => {
                collect_locals_expr(iterable, locals);
                collect_locals_pat(pat, locals);
                for statement in statements {
                    collect_locals_stmt(std::slice::from_ref(statement), locals);
                }
            }
        }
    }
}

fn collect_locals_pat(pat: &Rc<Pat>, locals: &mut HashSet<NodeId>) {
    match &*pat.kind {
        PatKind::Binding(_) => {
            locals.insert(pat.id);
        }
        PatKind::Tuple(pats) => {
            for pat in pats {
                collect_locals_pat(pat, locals);
            }
        }
        PatKind::Variant(_prefixes, _, Some(inner)) => {
            collect_locals_pat(inner, locals);
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

fn count_args(
    ctx: &StaticsContext,
    args: &[ArgMaybeAnnotated],
    overload_ty: Option<SolvedType>,
) -> usize {
    match overload_ty {
        Some(overload_ty) => {
            let SolvedType::Function(args, _) = overload_ty else { unreachable!() };
            args.iter().filter(|arg| **arg != SolvedType::Void).count()
        }
        None => args
            .iter()
            .filter(|arg| {
                let arg_ty = ctx.solution_of_node(arg.0.node()).unwrap();
                arg_ty != SolvedType::Void
            })
            .count(),
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

fn idx_of_field(
    statics: &StaticsContext,
    monomorph_env: &MonomorphEnv,
    accessed: &Rc<Expr>,
    field_name: &str,
) -> u16 {
    let accessed_ty = statics.solution_of_node(accessed.node()).unwrap();

    match accessed_ty {
        Type::Nominal(Nominal::Struct(struct_def), _) => {
            let mut index = 0;
            // TODO duplicated logic
            for field in &*struct_def.fields {
                if field.name.v == field_name {
                    return index as u16;
                }
                let field_ty = field
                    .ty
                    .to_solved_type(statics)
                    .unwrap()
                    .subst(monomorph_env);
                if field_ty != SolvedType::Void {
                    index += 1;
                }
            }
            panic!("could not find field")
        }
        _ => panic!("not a udt"),
    }
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
