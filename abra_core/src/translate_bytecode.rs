/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::assembly::{Instr, Label, Line, remove_labels};
use crate::ast::{
    AstNode, BinaryOperator, FuncDecl, FuncDef, InterfaceDecl, Item, ItemKind, TypeKind,
};
use crate::ast::{FileAst, FileDatabase, NodeId};
use crate::builtin::Builtin;
use crate::environment::Environment;
use crate::statics::typecheck::{Monotype, Nominal};
use crate::statics::{Declaration, TypeProv};
use crate::statics::{Type, ty_fits_impl_ty};
use crate::utils::hash::HashMap;
use crate::utils::hash::HashSet;
use crate::utils::id_set::IdSet;
use crate::vm::{AbraFloat, AbraInt, Instr as VmInstr};
use crate::{
    ast::{Expr, ExprKind, Pat, PatKind, Stmt, StmtKind},
    statics::StaticsContext,
};
use std::mem;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

type OffsetTable = HashMap<NodeId, i32>;
type Lambdas = HashMap<AstNode, LambdaData>;
type OverloadedFuncLabels = HashMap<OverloadedFuncDesc, Label>;
type MonomorphEnv = Environment<String, Type>;
pub(crate) type LabelMap = HashMap<Label, usize>;

#[derive(Debug, Clone, PartialOrd, Ord, PartialEq, Eq, Hash)]
struct OverloadedFuncDesc {
    name: String,
    impl_type: Monotype,
    func_def: Rc<FuncDef>,
}

#[derive(Debug, Clone)]
struct LambdaData {
    label: Label,
    offset_table: OffsetTable,
    nlocals: u16,
}

pub(crate) struct Translator {
    statics: StaticsContext,
    _files: FileDatabase,
    file_asts: Vec<Rc<FileAst>>,
}

#[derive(Debug, Default)]
struct TranslatorState {
    lines: Vec<Line>,
    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,
    function_name_arena: IdSet<String>,
    instr_count: usize,
    lambdas: Lambdas,
    overloaded_func_map: OverloadedFuncLabels,
    overloaded_methods_to_generate: Vec<(OverloadedFuncDesc, Type)>,
    loop_stack: Vec<EnclosingLoop>,
    return_stack: Vec<String>,
}

#[derive(Debug, Default)]
struct EnclosingLoop {
    start_label: String,
    end_label: String,
}

#[derive(Debug, Clone)]
pub struct CompiledProgram {
    pub(crate) instructions: Vec<VmInstr>,
    pub(crate) label_map: LabelMap,
    pub(crate) static_strings: Vec<String>,
    // debug data
    pub(crate) filename_arena: Vec<String>,
    pub(crate) function_name_arena: Vec<String>,
    pub(crate) filename_table: Vec<(BytecodeIndex, u32)>,
    pub(crate) lineno_table: Vec<(BytecodeIndex, u32)>,
    pub(crate) function_name_table: Vec<(BytecodeIndex, u32)>,
}

pub type BytecodeIndex = u32;

impl Declaration {
    pub fn to_bytecode_resolution(&self) -> BytecodeResolution {
        match self {
            Declaration::Var(node) => BytecodeResolution::Var(node.clone()),
            Declaration::FreeFunction(f, qname) => {
                BytecodeResolution::FreeFunction(f.clone(), qname.clone())
            }
            Declaration::_ForeignFunction {
                decl,
                libname,
                symbol,
            } => BytecodeResolution::ForeignFunction {
                decl: decl.clone(),
                libname: libname.clone(),
                symbol: symbol.clone(),
            },
            Declaration::HostFunction(f, fullname) => {
                BytecodeResolution::HostFunction(f.clone(), fullname.clone())
            }
            Declaration::InterfaceDef(_) => panic!(), // TODO: remove panic
            Declaration::InterfaceMethod {
                iface_def,
                method,
                fully_qualified_name,
            } => {
                BytecodeResolution::InterfaceMethod {
                    iface_def: iface_def.clone(),
                    method: *method,
                    fully_qualified_name: fully_qualified_name.clone(),
                } // TODO: don't use String here, just use iface_def and u16
            }
            Declaration::Enum(..) => BytecodeResolution::EnumDef,
            Declaration::EnumVariant { enum_def, variant } => {
                let data = &enum_def.variants[*variant as usize].data;
                let arity = match data {
                    None => 0,
                    Some(ty) => match &*ty.kind {
                        TypeKind::Poly(..)
                        | TypeKind::Named(_)
                        | TypeKind::NamedWithParams(..)
                        | TypeKind::Unit
                        | TypeKind::Int
                        | TypeKind::Float
                        | TypeKind::Bool
                        | TypeKind::Str
                        | TypeKind::Function(..) => 1,
                        TypeKind::Tuple(elems) => elems.len(),
                    },
                } as u16;
                BytecodeResolution::VariantCtor(*variant, arity)
            }
            Declaration::Struct(struct_def) => {
                let nargs = struct_def.fields.len() as u16;
                BytecodeResolution::StructCtor(nargs)
            }
            Declaration::Array => {
                panic!(); // TODO: remove panic
            }
            Declaration::Polytype(_) => {
                panic!(); // TODO: remove panic
            }
            Declaration::Builtin(b) => BytecodeResolution::Builtin(*b),
        }
    }
}

// TODO: Remove this type and just use Declaration
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum BytecodeResolution {
    Var(AstNode),
    FreeFunction(Rc<FuncDef>, String),
    HostFunction(Rc<FuncDecl>, String),
    ForeignFunction {
        decl: Rc<FuncDecl>,
        libname: PathBuf,
        symbol: String,
    },
    InterfaceMethod {
        iface_def: Rc<InterfaceDecl>,
        method: u16,
        fully_qualified_name: String,
    },
    StructCtor(u16),
    EnumDef,
    VariantCtor(u16, u16),
    Builtin(Builtin),
}

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

    fn emit(&self, st: &mut TranslatorState, i: impl Into<Line>) {
        let l: Line = i.into();

        if let Line::Instr(_) = &l {
            st.instr_count += 1;
        }

        st.lines.push(l);
    }

    fn update_filename_lineno_tables(&self, st: &mut TranslatorState, node: AstNode) {
        let location = node.location();
        let file_id = location.file_id;

        let file = self._files.get(file_id).unwrap();
        let line_no = file.line_number_for_index(location.lo as usize);

        let bytecode_index = st.instr_count;
        {
            let mut redundant = false;
            if let Some(last) = st.filename_table.last() {
                if last.1 == file_id {
                    redundant = true;
                }
            }
            if !redundant {
                st.filename_table.push((bytecode_index as u32, file_id));
            }
        }

        {
            let mut redundant = false;
            if let Some(last) = st.lineno_table.last() {
                if last.1 == line_no as u32 {
                    redundant = true;
                }
            }
            if !redundant {
                st.lineno_table
                    .push((bytecode_index as u32, line_no as u32));
            }
        }
    }

    fn update_function_name_table(&self, st: &mut TranslatorState, name: &str) {
        let bytecode_index = st.instr_count;

        let function_name_id = st.function_name_arena.insert(name.to_string());

        let mut redundant = false;
        if let Some(last) = st.function_name_table.last() {
            if last.1 == function_name_id {
                redundant = true;
            }
        }
        if !redundant {
            st.function_name_table
                .push((bytecode_index as u32, function_name_id));
        }
    }

    pub(crate) fn translate(&mut self) -> CompiledProgram {
        let mut st = TranslatorState::default();
        {
            let st = &mut st;

            let monomorph_env = MonomorphEnv::empty();

            // Initialization routine before main function (load shared libraries)
            // dbg!(&self.statics.dylib_to_funcs);
            // for (l, symbols) in &self.statics.dylib_to_funcs {
            //     self.emit(st, Instr::PushString(l.to_str().unwrap().to_string()));
            //     self.emit(st, Instr::LoadLib);
            //     for s in symbols {
            //         self.emit(st, Instr::PushString(s.to_string()));
            //         self.emit(st, Instr::LoadForeignFunc);
            //     }
            // }
            for (i, lib) in self.statics.dylibs.iter().enumerate() {
                self.emit(st, Instr::PushString(lib.to_str().unwrap().to_string()));
                self.emit(st, Instr::LoadLib);
                // TODO: &(i as u32) is dumb
                for s in self.statics.dylib_to_funcs2[&(i as u32)].iter() {
                    self.emit(st, Instr::PushString(s.to_string()));
                    self.emit(st, Instr::LoadForeignFunc);
                }
            }

            // Handle the main function (files)
            if let Some(file) = self.file_asts.first() {
                let file = file.clone();
                let mut locals = HashSet::default();

                // use filename as name of function in this case
                self.update_function_name_table(st, "<main>");

                let stmts: Vec<_> = file
                    .items
                    .iter()
                    .filter_map(|item| match &*item.kind {
                        ItemKind::Stmt(stmt) => Some(stmt.clone()),
                        _ => None,
                    })
                    .collect();
                collect_locals_stmt(&stmts, &mut locals);

                for _ in 0..locals.len() {
                    self.emit(st, Instr::PushNil);
                }
                let mut offset_table = OffsetTable::default();
                for (i, local) in locals.iter().enumerate() {
                    offset_table.entry(*local).or_insert((i) as i32);
                }
                for (i, item) in file.items.iter().enumerate() {
                    if let ItemKind::Stmt(stmt) = &*item.kind {
                        self.translate_stmt(
                            stmt.clone(),
                            i == file.items.len() - 1,
                            &offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                    }
                }
                self.emit(st, Instr::Return);
            }

            // Handle ordinary function (not overloaded, not a closure) definitions
            let files = self.file_asts.clone();
            for file in files {
                for item in &file.items {
                    self.translate_item_static(item.clone(), st, false);
                }
            }

            while !st.lambdas.is_empty() || !st.overloaded_methods_to_generate.is_empty() {
                // Handle lambdas with captures
                let mut iteration = HashMap::default();
                mem::swap(&mut (iteration), &mut st.lambdas);
                for (node, data) in iteration {
                    let AstNode::Expr(expr) = node else { panic!() };
                    let ExprKind::AnonymousFunction(args, _, body) = &*expr.kind else {
                        panic!() // TODO: get rid of this panic
                    };

                    self.update_function_name_table(st, "<anonymous fn>");

                    self.emit(st, Line::Label(data.label));

                    for _ in 0..data.nlocals {
                        self.emit(st, Instr::PushNil);
                    }

                    self.translate_expr(
                        body.clone(),
                        &data.offset_table,
                        monomorph_env.clone(),
                        st,
                    );

                    let nlocals = data.nlocals;
                    let nargs = args.len() as u16;
                    if nlocals + nargs > 0 {
                        // pop all locals and arguments except one. The last one is the return value slot.
                        self.emit(st, Instr::StoreOffset(-(nargs as i32)));
                        for _ in 0..(nlocals + nargs - 1) {
                            self.emit(st, Instr::Pop);
                        }
                    }

                    self.emit(st, Instr::Return);
                }

                // Handle interface method implementations
                let mut iteration = Vec::new();
                mem::swap(&mut (iteration), &mut st.overloaded_methods_to_generate);
                for (desc, substituted_ty) in iteration {
                    let f = desc.func_def.clone();

                    self.update_function_name_table(st, &f.name.v);

                    let overloaded_func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
                    let monomorph_env = MonomorphEnv::empty();
                    update_monomorph_env(monomorph_env.clone(), overloaded_func_ty, substituted_ty);

                    let label = st.overloaded_func_map.get(&desc).unwrap();
                    self.emit(st, Line::Label(label.clone()));

                    let mut locals = HashSet::default();
                    collect_locals_expr(&f.body, &mut locals);
                    let locals_count = locals.len();
                    for _ in 0..locals_count {
                        self.emit(st, Instr::PushNil);
                    }
                    let mut offset_table = OffsetTable::default();
                    for (i, arg) in f.args.iter().rev().enumerate() {
                        offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
                    }
                    for (i, local) in locals.iter().enumerate() {
                        offset_table.entry(*local).or_insert((i) as i32);
                    }
                    let nargs = f.args.len();
                    self.translate_expr(f.body.clone(), &offset_table, monomorph_env.clone(), st);

                    if locals_count + nargs > 0 {
                        // pop all locals and arguments except one. The last one is the return value slot.
                        self.emit(st, Instr::StoreOffset(-(nargs as i32)));
                        for _ in 0..(locals_count + nargs - 1) {
                            self.emit(st, Instr::Pop);
                        }
                    }

                    self.emit(st, Instr::Return);
                }
            }
        }
        let (instructions, label_map) = remove_labels(&st.lines, &self.statics.string_constants);
        let string_table: Vec<_> = self.statics.string_constants.clone().into_iter().collect();
        let mut filename_arena = vec![];
        for file_data in self._files.files.iter() {
            filename_arena.push(file_data.name().to_string());
        }
        CompiledProgram {
            instructions,
            label_map,
            static_strings: string_table,
            filename_arena,
            function_name_arena: st.function_name_arena.into_iter().collect(),
            filename_table: st.filename_table,
            lineno_table: st.lineno_table,
            function_name_table: st.function_name_table,
        }
    }

    fn translate_expr(
        &mut self, // TODO: make this immutable, and all other occurrences. It's only mutable right now because of ty_fits_impl_ty calls ast_type_to_statics_type...
        expr: Rc<Expr>,
        offset_table: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_filename_lineno_tables(st, expr.node());
        match &*expr.kind {
            ExprKind::Variable(_) => {
                match self
                    .statics
                    .resolution_map
                    .get(&expr.id)
                    .unwrap()
                    .to_bytecode_resolution()
                {
                    BytecodeResolution::VariantCtor(tag, _) => {
                        self.emit(st, Instr::PushNil);
                        self.emit(st, Instr::ConstructVariant { tag });
                    }
                    BytecodeResolution::Var(node) => {
                        let idx = offset_table.get(&node.id()).unwrap();
                        self.emit(st, Instr::LoadOffset(*idx));
                    }
                    BytecodeResolution::Builtin(b) => {
                        match b {
                            Builtin::Newline => {
                                self.emit(st, Instr::PushString("\n".to_owned()));
                            }
                            _ => {
                                // TODO: generate functions for builtins
                                unimplemented!()
                            }
                        }
                    }
                    BytecodeResolution::FreeFunction(_, name) => {
                        self.emit(
                            st,
                            Instr::MakeClosure {
                                func_addr: name.clone(),
                            },
                        );
                    }
                    BytecodeResolution::StructCtor(_)
                    | BytecodeResolution::ForeignFunction { .. }
                    | BytecodeResolution::HostFunction(..)
                    | BytecodeResolution::InterfaceMethod { .. }
                    | BytecodeResolution::EnumDef { .. } => unimplemented!(),
                }
            }
            ExprKind::MemberAccessInferred(ident) => {
                match self
                    .statics
                    .resolution_map
                    .get(&ident.id)
                    .unwrap()
                    .to_bytecode_resolution()
                {
                    BytecodeResolution::VariantCtor(tag, _) => {
                        self.emit(st, Instr::PushNil);
                        self.emit(st, Instr::ConstructVariant { tag });
                    }
                    _ => panic!(),
                }
            }
            ExprKind::Unit => {
                self.emit(st, Instr::PushNil);
            }
            ExprKind::Bool(b) => {
                self.emit(st, Instr::PushBool(*b));
            }
            ExprKind::Int(i) => {
                self.emit(st, Instr::PushInt(*i));
            }
            ExprKind::Float(f) => {
                self.emit(st, Instr::PushFloat(f.parse::<AbraFloat>().unwrap()));
            }
            ExprKind::Str(s) => {
                self.emit(st, Instr::PushString(s.clone()));
            }
            ExprKind::BinOp(left, op, right) => {
                self.translate_expr(left.clone(), offset_table, monomorph_env.clone(), st);
                self.translate_expr(right.clone(), offset_table, monomorph_env.clone(), st);
                match op {
                    BinaryOperator::Add => self.emit(st, Instr::Add),
                    BinaryOperator::Subtract => self.emit(st, Instr::Subtract),
                    BinaryOperator::Multiply => self.emit(st, Instr::Multiply),
                    BinaryOperator::Divide => self.emit(st, Instr::Divide),
                    BinaryOperator::GreaterThan => self.emit(st, Instr::GreaterThan),
                    BinaryOperator::LessThan => self.emit(st, Instr::LessThan),
                    BinaryOperator::GreaterThanOrEqual => self.emit(st, Instr::GreaterThanOrEqual),
                    BinaryOperator::LessThanOrEqual => self.emit(st, Instr::LessThanOrEqual),
                    BinaryOperator::Equal => self.emit(st, Instr::Equal),
                    BinaryOperator::Format => {
                        // TODO: translate_bytecode shouldn't have to fish around in statics.global_namespace just for prelude.format_append or similar
                        let format_append_decl = self
                            .statics
                            .root_namespace
                            .get_declaration("prelude.format_append")
                            .unwrap();
                        let Declaration::FreeFunction(func, func_name) = format_append_decl else {
                            panic!()
                        };

                        // TODO: This is way too much work for translate_bytecode to do
                        let arg1_ty = self.statics.solution_of_node(left.node()).unwrap();
                        let arg2_ty = self.statics.solution_of_node(right.node()).unwrap();
                        let out_ty = self.statics.solution_of_node(expr.node()).unwrap();
                        let specific_func_ty =
                            Type::Function(vec![arg1_ty, arg2_ty], out_ty.into());

                        let substituted_ty =
                            subst_with_monomorphic_env(monomorph_env, specific_func_ty);

                        self.handle_overloaded_func(st, substituted_ty, &func_name, func.clone());
                    }
                    BinaryOperator::Or => self.emit(st, Instr::Or),
                    BinaryOperator::And => self.emit(st, Instr::And),
                    BinaryOperator::Pow => self.emit(st, Instr::Power),
                    BinaryOperator::Mod => self.emit(st, Instr::Modulo),
                }
            }
            ExprKind::FuncAp(func, args) => {
                for arg in args {
                    self.translate_expr(arg.clone(), offset_table, monomorph_env.clone(), st);
                }
                let resolution = match &*func.kind {
                    ExprKind::Variable(_) => self
                        .statics
                        .resolution_map
                        .get(&func.id)
                        .unwrap()
                        .to_bytecode_resolution(),
                    ExprKind::MemberAccess(_prefix, ident) => self
                        .statics
                        .resolution_map
                        .get(&ident.id)
                        .unwrap()
                        .to_bytecode_resolution(),
                    ExprKind::MemberAccessInferred(..) => unimplemented!(),

                    ExprKind::Unit
                    | ExprKind::Int(_)
                    | ExprKind::Float(_)
                    | ExprKind::Bool(_)
                    | ExprKind::Str(_)
                    | ExprKind::List(_)
                    | ExprKind::Array(_)
                    | ExprKind::WhileLoop(..)
                    | ExprKind::BinOp(..)
                    | ExprKind::Tuple(..) => panic!("lhs of FuncAp not a function"),

                    ExprKind::If(_expr, _expr1, _expr2) => unimplemented!(),
                    ExprKind::Match(_expr, _match_armss) => unimplemented!(),
                    ExprKind::Block(_stmts) => unimplemented!(),
                    ExprKind::IndexAccess(_expr, _expr1) => unimplemented!(),
                    ExprKind::FuncAp(_expr, _exprs) => unimplemented!(),
                    ExprKind::AnonymousFunction(_items, _, _expr) => unimplemented!(),
                };
                match resolution {
                    BytecodeResolution::Var(node) => {
                        // assume it's a function object
                        let idx = offset_table.get(&node.id()).unwrap();
                        self.emit(st, Instr::LoadOffset(*idx));
                        self.emit(st, Instr::CallFuncObj);
                    }
                    BytecodeResolution::FreeFunction(f, name) => {
                        let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
                        if !func_ty.is_overloaded() {
                            self.emit(st, Instr::Call(name.clone()));
                        } else {
                            let specific_func_ty =
                                self.statics.solution_of_node(func.node()).unwrap();

                            let substituted_ty =
                                subst_with_monomorphic_env(monomorph_env, specific_func_ty);

                            self.handle_overloaded_func(st, substituted_ty, &name, f.clone());
                        }
                    }
                    BytecodeResolution::HostFunction(decl, _) => {
                        let idx = self.statics.host_funcs.get_id(&decl.name.v) as u16;
                        self.emit(st, Instr::HostFunc(idx));
                    }
                    BytecodeResolution::ForeignFunction {
                        decl: _decl,
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
                        let lib_id = self.statics.dylibs.get_id(&libname);
                        let func_id = self.statics.dylib_to_funcs2[&lib_id].get_id(&symbol);
                        self.emit(st, Instr::CallExtern(func_id as usize));
                    }
                    BytecodeResolution::InterfaceMethod {
                        iface_def,
                        method,
                        fully_qualified_name,
                    } => {
                        let func_ty = self.statics.solution_of_node(func.node()).unwrap();
                        let substituted_ty =
                            subst_with_monomorphic_env(monomorph_env.clone(), func_ty);
                        let method_name = &iface_def.methods[method as usize].name.v;
                        let impl_list = self
                            .statics
                            .interface_impls
                            .get(&iface_def)
                            .unwrap()
                            .clone();

                        // TODO: simplify this logic
                        for imp in impl_list {
                            for f in &imp.methods {
                                if f.name.v == *method_name {
                                    let unifvar = self
                                        .statics
                                        .unifvars
                                        .get(&TypeProv::Node(f.name.node()))
                                        .unwrap();
                                    let interface_impl_ty = unifvar.solution().unwrap();

                                    if ty_fits_impl_ty(
                                        &self.statics,
                                        substituted_ty.clone(),
                                        interface_impl_ty,
                                    )
                                    .is_ok()
                                    {
                                        self.handle_overloaded_func(
                                            st,
                                            substituted_ty.clone(),
                                            &fully_qualified_name,
                                            f.clone(),
                                        );
                                    }
                                }
                            }
                        }
                    }
                    BytecodeResolution::StructCtor(nargs) => {
                        self.emit(st, Instr::Construct(nargs));
                    }
                    BytecodeResolution::VariantCtor(tag, nargs) => {
                        if nargs > 1 {
                            // turn the arguments (associated data) into a tuple
                            self.emit(st, Instr::Construct(nargs));
                        }
                        self.emit(st, Instr::ConstructVariant { tag });
                    }
                    BytecodeResolution::EnumDef { .. } => {
                        panic!("can't call enum name as ctor");
                    }
                    BytecodeResolution::Builtin(b) => match b {
                        Builtin::AddInt => {
                            self.emit(st, Instr::Add);
                        }
                        Builtin::SubtractInt => {
                            self.emit(st, Instr::Subtract);
                        }
                        Builtin::MultiplyInt => {
                            self.emit(st, Instr::Multiply);
                        }
                        Builtin::DivideInt => {
                            self.emit(st, Instr::Divide);
                        }
                        Builtin::PowerInt => {
                            self.emit(st, Instr::Power);
                        }
                        Builtin::ModuloInt => {
                            self.emit(st, Instr::Modulo);
                        }
                        Builtin::SqrtInt => {
                            self.emit(st, Instr::SquareRoot);
                        }
                        Builtin::AddFloat => {
                            self.emit(st, Instr::Add);
                        }
                        Builtin::SubtractFloat => {
                            self.emit(st, Instr::Subtract);
                        }
                        Builtin::MultiplyFloat => {
                            self.emit(st, Instr::Multiply);
                        }
                        Builtin::DivideFloat => {
                            self.emit(st, Instr::Divide);
                        }
                        Builtin::ModuloFloat => {
                            self.emit(st, Instr::Modulo);
                        }
                        Builtin::PowerFloat => {
                            self.emit(st, Instr::Power);
                        }
                        Builtin::SqrtFloat => {
                            self.emit(st, Instr::SquareRoot);
                        }
                        Builtin::LessThanInt => {
                            self.emit(st, Instr::LessThan);
                        }
                        Builtin::LessThanOrEqualInt => {
                            self.emit(st, Instr::LessThanOrEqual);
                        }
                        Builtin::GreaterThanInt => {
                            self.emit(st, Instr::GreaterThan);
                        }
                        Builtin::GreaterThanOrEqualInt => {
                            self.emit(st, Instr::GreaterThanOrEqual);
                        }
                        Builtin::EqualInt => {
                            self.emit(st, Instr::Equal);
                        }
                        Builtin::LessThanFloat => {
                            self.emit(st, Instr::LessThan);
                        }
                        Builtin::LessThanOrEqualFloat => {
                            self.emit(st, Instr::LessThanOrEqual);
                        }
                        Builtin::GreaterThanFloat => {
                            self.emit(st, Instr::GreaterThan);
                        }
                        Builtin::GreaterThanOrEqualFloat => {
                            self.emit(st, Instr::GreaterThanOrEqual);
                        }
                        Builtin::EqualFloat => {
                            self.emit(st, Instr::Equal);
                        }
                        Builtin::EqualString => {
                            self.emit(st, Instr::Equal);
                        }
                        Builtin::IntToString => {
                            self.emit(st, Instr::IntToString);
                        }
                        Builtin::FloatToString => {
                            self.emit(st, Instr::FloatToString);
                        }
                        Builtin::ConcatStrings => {
                            self.emit(st, Instr::ConcatStrings);
                        }
                        Builtin::ArrayAppend => {
                            self.emit(st, Instr::ArrayAppend);
                        }
                        Builtin::ArrayLength => {
                            self.emit(st, Instr::ArrayLength);
                        }
                        Builtin::ArrayPop => {
                            self.emit(st, Instr::ArrayPop);
                        }
                        Builtin::Panic => {
                            self.emit(st, Instr::Panic);
                        }
                        Builtin::Newline => {
                            panic!("not a function");
                        }
                    },
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
                self.emit(st, Instr::Construct(exprs.len() as u16));
            }
            ExprKind::If(cond, then_block, Some(else_block)) => {
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                self.emit(st, Instr::JumpIf(then_label.clone()));
                self.translate_expr(else_block.clone(), offset_table, monomorph_env.clone(), st);
                self.emit(st, Instr::Jump(end_label.clone()));
                self.emit(st, Line::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, monomorph_env.clone(), st);
                self.emit(st, Line::Label(end_label));
            }
            ExprKind::If(cond, then_block, None) => {
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                self.emit(st, Instr::JumpIf(then_label.clone()));
                self.emit(st, Instr::Jump(end_label.clone()));
                self.emit(st, Line::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, monomorph_env.clone(), st);
                self.emit(st, Line::Label(end_label));
                self.emit(st, Instr::PushNil); // TODO get rid of this unnecessary overhead
            }
            ExprKind::MemberAccess(accessed, field_name) => {
                if let Some(BytecodeResolution::VariantCtor(tag, _)) = self
                    .statics
                    .resolution_map
                    .get(&field_name.id)
                    .map(Declaration::to_bytecode_resolution)
                {
                    self.emit(st, Instr::PushNil);
                    self.emit(st, Instr::ConstructVariant { tag });
                } else {
                    self.translate_expr(accessed.clone(), offset_table, monomorph_env.clone(), st);
                    let idx = idx_of_field(&self.statics, accessed.clone(), &field_name.v);
                    self.emit(st, Instr::GetField(idx));
                }
            }
            ExprKind::Array(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                }
                self.emit(st, Instr::Construct(exprs.len() as u16));
            }
            ExprKind::List(exprs) => {
                fn translate_list(
                    translator: &mut Translator,
                    exprs: &[Rc<Expr>],
                    offset_table: &OffsetTable,
                    monomorph_env: MonomorphEnv,
                    st: &mut TranslatorState,
                ) {
                    if exprs.is_empty() {
                        translator.emit(st, Instr::PushNil);
                        translator.emit(st, Instr::ConstructVariant { tag: 0 });
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
                        translator.emit(st, Instr::Construct(2)); // (head, tail)
                        translator.emit(st, Instr::ConstructVariant { tag: 1 });
                    }
                }

                translate_list(self, exprs, offset_table, monomorph_env.clone(), st);
            }
            ExprKind::IndexAccess(array, index) => {
                self.translate_expr(index.clone(), offset_table, monomorph_env.clone(), st);
                self.translate_expr(array.clone(), offset_table, monomorph_env.clone(), st);
                self.emit(st, Instr::GetIdx);
            }
            ExprKind::Match(expr, arms) => {
                let ty = self.statics.solution_of_node(expr.node()).unwrap();

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
                    self.emit(st, Instr::Duplicate);
                    self.translate_pat_comparison(&ty, arm.pat.clone(), st);
                    self.emit(st, Instr::JumpIf(arm_label));
                }
                for (i, arm) in arms.iter().enumerate() {
                    self.emit(st, Line::Label(arm_labels[i].clone()));

                    self.handle_pat_binding(arm.pat.clone(), offset_table, st);

                    self.translate_expr(arm.expr.clone(), offset_table, monomorph_env.clone(), st);
                    if i != arms.len() - 1 {
                        self.emit(st, Instr::Jump(end_label.clone()));
                    }
                }
                self.emit(st, Line::Label(end_label));
            }
            ExprKind::AnonymousFunction(args, _, body) => {
                let label = make_label("lambda");

                let mut locals = HashSet::default();
                collect_locals_expr(body, &mut locals);
                let locals_count = locals.len() as u16;

                let mut lambda_offset_table = OffsetTable::default();
                for (i, arg) in args.iter().rev().enumerate() {
                    lambda_offset_table
                        .entry(arg.0.id)
                        .or_insert(-(i as i32) - 1);
                }

                st.lambdas.insert(
                    expr.node(),
                    LambdaData {
                        label: label.clone(),
                        offset_table: lambda_offset_table,
                        nlocals: locals_count,
                    },
                );

                self.emit(st, Instr::MakeClosure { func_addr: label });
            }
            ExprKind::WhileLoop(cond, body) => {
                let start_label = make_label("while_start");
                let end_label = make_label("while_end");

                self.emit(st, Line::Label(start_label.clone()));
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                self.emit(st, Instr::Not);
                self.emit(st, Instr::JumpIf(end_label.clone()));
                st.loop_stack.push(EnclosingLoop {
                    start_label: start_label.clone(),
                    end_label: end_label.clone(),
                });
                self.translate_expr(body.clone(), offset_table, monomorph_env.clone(), st);
                st.loop_stack.pop();
                self.emit(st, Instr::Pop);
                self.emit(st, Instr::Jump(start_label));
                self.emit(st, Line::Label(end_label));
                self.emit(st, Instr::PushNil);
            }
        }
    }

    // emit items for checking if a pattern matches the TOS, replacing it with a boolean
    fn translate_pat_comparison(
        &self,
        scrutinee_ty: &Type,
        pat: Rc<Pat>,
        st: &mut TranslatorState,
    ) {
        match &*pat.kind {
            PatKind::Wildcard | PatKind::Binding(_) | PatKind::Unit => {
                self.emit(st, Instr::Pop);
                self.emit(st, Instr::PushBool(true));
                return;
            }
            _ => {}
        }

        match scrutinee_ty {
            Type::Int => match &*pat.kind {
                PatKind::Int(i) => {
                    self.emit(st, Instr::PushInt(*i));
                    self.emit(st, Instr::Equal);
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::Bool => match &*pat.kind {
                PatKind::Bool(b) => {
                    self.emit(st, Instr::PushBool(*b));
                    self.emit(st, Instr::Equal);
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::String => match &*pat.kind {
                PatKind::Str(s) => {
                    self.emit(st, Instr::PushString(s.clone()));
                    self.emit(st, Instr::Equal);
                }
                _ => panic!("unexpected pattern: {:?}", pat.kind),
            },
            Type::Nominal(_, _) => match &*pat.kind {
                PatKind::Variant(_prefixes, ctor, inner) => {
                    let BytecodeResolution::VariantCtor(tag, _) = self
                        .statics
                        .resolution_map
                        .get(&ctor.id)
                        .unwrap()
                        .to_bytecode_resolution()
                    else {
                        panic!("expected variableto be defined in node");
                    };
                    let tag_fail_label = make_label("tag_fail");
                    let end_label = make_label("endvariant");

                    self.emit(st, Instr::Deconstruct);
                    self.emit(st, Instr::PushInt(tag as AbraInt));
                    self.emit(st, Instr::Equal);
                    self.emit(st, Instr::Not);
                    self.emit(st, Instr::JumpIf(tag_fail_label.clone()));

                    if let Some(inner) = inner {
                        let inner_ty = self.statics.solution_of_node(inner.node()).unwrap();
                        self.translate_pat_comparison(&inner_ty, inner.clone(), st);
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
                    self.emit(st, Instr::Deconstruct);
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
                        self.emit(st, Instr::Not);
                        self.emit(st, Instr::JumpIf(failure_labels[i].clone()));
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
                    for label in &failure_labels[1..] {
                        self.emit(st, Instr::Pop);
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

    fn translate_item_static(
        &mut self,
        stmt: Rc<Item>,
        st: &mut TranslatorState,
        iface_method: bool,
    ) {
        match &*stmt.kind {
            ItemKind::Stmt(_) => {}
            ItemKind::InterfaceImpl(iface_impl) => {
                for f in &iface_impl.methods {
                    self.translate_iface_method(f, st, true);
                }
            }

            ItemKind::FuncDef(f) => {
                // (this could be an overloaded function or an interface method)
                let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();

                if func_ty.is_overloaded() // println: 'a ToString -> ()
                || iface_method
                // to_string: 'a ToString -> String
                {
                    return;
                }

                let Some(BytecodeResolution::FreeFunction(_, fully_qualified_name)) = self
                    .statics
                    .resolution_map
                    .get(&f.name.id)
                    .map(Declaration::to_bytecode_resolution)
                else {
                    panic!()
                };

                self.update_function_name_table(st, &f.name.v);

                let return_label = make_label("return");

                self.emit(st, Line::Label(fully_qualified_name.clone()));
                let mut locals = HashSet::default();
                collect_locals_expr(&f.body, &mut locals);
                let locals_count = locals.len();
                for _ in 0..locals_count {
                    self.emit(st, Instr::PushNil);
                }
                let mut offset_table = OffsetTable::default();
                for (i, arg) in f.args.iter().rev().enumerate() {
                    offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
                }
                for (i, local) in locals.iter().enumerate() {
                    offset_table.entry(*local).or_insert((i) as i32);
                }
                let nargs = f.args.len();

                st.return_stack.push(return_label.clone());
                self.translate_expr(f.body.clone(), &offset_table, MonomorphEnv::empty(), st);
                st.return_stack.pop();

                self.emit(st, return_label);

                if locals_count + nargs > 0 {
                    // pop all locals and arguments except one. The last one is the return value slot.
                    self.emit(st, Instr::StoreOffset(-(nargs as i32)));
                    for _ in 0..(locals_count + nargs - 1) {
                        self.emit(st, Instr::Pop);
                    }
                }

                self.emit(st, Instr::Return);
            }
            ItemKind::InterfaceDef(..)
            | ItemKind::TypeDef(..)
            | ItemKind::Import(..)
            | ItemKind::HostFuncDecl(..)
            | ItemKind::ForeignFuncDecl(..) => {
                // noop
            }
        }
    }

    fn translate_iface_method(
        &mut self,
        f: &Rc<FuncDef>,
        st: &mut TranslatorState,
        iface_method: bool,
    ) {
        {
            let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
            let func_name = f.name.v.clone();

            if func_ty.is_overloaded() // println: 'a ToString -> ()
                || iface_method
            // to_string: 'a ToString -> String
            {
                return;
            }

            self.update_function_name_table(st, &func_name);

            self.emit(st, Line::Label(func_name));
            let mut locals = HashSet::default();
            collect_locals_expr(&f.body, &mut locals);
            let locals_count = locals.len();
            for _ in 0..locals_count {
                self.emit(st, Instr::PushNil);
            }
            let mut offset_table = OffsetTable::default();
            for (i, arg) in f.args.iter().rev().enumerate() {
                offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
            }
            for (i, local) in locals.iter().enumerate() {
                offset_table.entry(*local).or_insert((i) as i32);
            }
            let nargs = f.args.len();
            self.translate_expr(f.body.clone(), &offset_table, MonomorphEnv::empty(), st);

            if locals_count + nargs > 0 {
                // pop all locals and arguments except one. The last one is the return value slot.
                self.emit(st, Instr::StoreOffset(-(nargs as i32)));
                for _ in 0..(locals_count + nargs - 1) {
                    self.emit(st, Instr::Pop);
                }
            }

            self.emit(st, Instr::Return);
        }
    }

    fn translate_stmt(
        &mut self,
        stmt: Rc<Stmt>,
        is_last: bool,
        locals: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_filename_lineno_tables(st, stmt.node());
        match &*stmt.kind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr.clone(), locals, monomorph_env.clone(), st);
                self.handle_pat_binding(pat.0.clone(), locals, st);

                // TODO: again, unnecessary overhead, and bug prone
                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::Set(expr1, rvalue) => {
                match &*expr1.kind {
                    ExprKind::Variable(_) => {
                        let BytecodeResolution::Var(node) = self
                            .statics
                            .resolution_map
                            .get(&expr1.id)
                            .unwrap()
                            .to_bytecode_resolution()
                        else {
                            panic!("expected variableto be defined in node");
                        };
                        let idx = locals.get(&node.id()).unwrap();
                        self.translate_expr(rvalue.clone(), locals, monomorph_env.clone(), st);
                        self.emit(st, Instr::StoreOffset(*idx));
                    }
                    ExprKind::MemberAccess(accessed, field_name) => {
                        self.translate_expr(rvalue.clone(), locals, monomorph_env.clone(), st);
                        self.translate_expr(accessed.clone(), locals, monomorph_env.clone(), st);
                        let idx = idx_of_field(&self.statics, accessed.clone(), &field_name.v);
                        self.emit(st, Instr::SetField(idx));
                    }
                    ExprKind::IndexAccess(array, index) => {
                        self.translate_expr(rvalue.clone(), locals, monomorph_env.clone(), st);
                        self.translate_expr(index.clone(), locals, monomorph_env.clone(), st);
                        self.translate_expr(array.clone(), locals, monomorph_env.clone(), st);
                        self.emit(st, Instr::SetIdx);
                    }
                    _ => unimplemented!(),
                }
                // TODO: again, unnecessary overhead, and bug prone
                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), locals, monomorph_env.clone(), st);
                if !is_last {
                    self.emit(st, Instr::Pop);
                }
            }
            // TODO: should continue and break leave a Nil on the stack? Add tests for this!
            StmtKind::Break => {
                let enclosing_loop = st.loop_stack.last().unwrap();
                self.emit(st, Instr::Jump(enclosing_loop.end_label.clone()));

                // TODO: again, unnecessary overhead, and bug prone
                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::Continue => {
                let enclosing_loop = st.loop_stack.last().unwrap();
                self.emit(st, Instr::Jump(enclosing_loop.start_label.clone()));

                // TODO: again, unnecessary overhead, and bug prone
                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::Return(expr) => {
                self.translate_expr(expr.clone(), locals, monomorph_env.clone(), st);
                let return_label = st.return_stack.last().unwrap();
                self.emit(st, Instr::Jump(return_label.clone()));
            }
        }
    }

    fn handle_overloaded_func(
        &self,
        st: &mut TranslatorState,
        substituted_ty: Type,
        func_name: &String,
        func_def: Rc<FuncDef>,
    ) {
        let instance_ty = substituted_ty.monotype().unwrap();
        let entry = st.overloaded_func_map.entry(OverloadedFuncDesc {
            name: func_name.clone(),
            impl_type: instance_ty.clone(),
            func_def: func_def.clone(),
        });
        let label = match entry {
            std::collections::hash_map::Entry::Occupied(o) => o.get().clone(),
            std::collections::hash_map::Entry::Vacant(v) => {
                st.overloaded_methods_to_generate.push((
                    OverloadedFuncDesc {
                        name: func_name.clone(),
                        impl_type: instance_ty.clone(),
                        func_def: func_def.clone(),
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
        self.emit(st, Instr::Call(label));
    }

    fn handle_pat_binding(&self, pat: Rc<Pat>, locals: &OffsetTable, st: &mut TranslatorState) {
        let _ = self; // avoid warning

        match &*pat.kind {
            PatKind::Binding(_) => {
                // self.display_node(pat.id);
                let idx = locals.get(&pat.id).unwrap();
                self.emit(st, Instr::StoreOffset(*idx));
            }
            PatKind::Tuple(pats) => {
                self.emit(st, Instr::Deconstruct);
                for pat in pats.iter() {
                    self.handle_pat_binding(pat.clone(), locals, st);
                }
            }
            PatKind::Variant(_prefixes, _, inner) => {
                if let Some(inner) = inner {
                    // unpack tag and associated data
                    self.emit(st, Instr::Deconstruct);
                    // pop tag
                    self.emit(st, Instr::Pop);
                    self.handle_pat_binding(inner.clone(), locals, st);
                } else {
                    self.emit(st, Instr::Pop);
                }
            }
            PatKind::Unit
            | PatKind::Bool(..)
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
        ExprKind::MemberAccess(accessed, _) => {
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
        ExprKind::AnonymousFunction(..)
        | ExprKind::MemberAccessInferred(..)
        | ExprKind::Variable(..)
        | ExprKind::Unit
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
            StmtKind::Let(_, pat, _) => {
                collect_locals_pat(pat.0.clone(), locals);
            }
            StmtKind::Set(..) | StmtKind::Continue | StmtKind::Break => {}
            StmtKind::Return(expr) => {
                collect_locals_expr(expr, locals);
            }
        }
    }
}

fn collect_locals_pat(pat: Rc<Pat>, locals: &mut HashSet<NodeId>) {
    match &*pat.kind {
        PatKind::Binding(_) => {
            locals.insert(pat.id);
        }
        PatKind::Tuple(pats) => {
            for pat in pats {
                collect_locals_pat(pat.clone(), locals);
            }
        }
        PatKind::Variant(_prefixes, _, Some(inner)) => {
            collect_locals_pat(inner.clone(), locals);
        }
        PatKind::Variant(_prefixes, _, None) => {}
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
    static ID_COUNTER: AtomicUsize = AtomicUsize::new(1);
    let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
    format!("{}__#{:X}", hint, id)
}

fn idx_of_field(statics: &StaticsContext, accessed: Rc<Expr>, field: &str) -> u16 {
    let accessed_ty = statics.solution_of_node(accessed.node()).unwrap();

    match accessed_ty {
        Type::Nominal(Nominal::Struct(struct_def), _) => {
            let field_idx = struct_def
                .fields
                .iter()
                .position(|f| f.name.v == field)
                .unwrap();
            field_idx as u16
        }
        _ => panic!("not a udt"),
    }
}

fn update_monomorph_env(monomorph_env: MonomorphEnv, overloaded_ty: Type, monomorphic_ty: Type) {
    match (overloaded_ty, monomorphic_ty.clone()) {
        // recurse
        (Type::Function(args, out), Type::Function(args2, out2)) => {
            for i in 0..args.len() {
                update_monomorph_env(monomorph_env.clone(), args[i].clone(), args2[i].clone());
            }
            update_monomorph_env(monomorph_env, *out, *out2);
        }
        (Type::Nominal(ident, params), Type::Nominal(ident2, params2)) => {
            assert_eq!(ident, ident2);
            for i in 0..params.len() {
                update_monomorph_env(monomorph_env.clone(), params[i].clone(), params2[i].clone());
            }
        }
        (Type::Poly(polyty), _) => {
            monomorph_env.extend(polyty.name.v.clone(), monomorphic_ty);
        }
        (Type::Tuple(elems1), Type::Tuple(elems2)) => {
            for i in 0..elems1.len() {
                update_monomorph_env(monomorph_env.clone(), elems1[i].clone(), elems2[i].clone());
            }
        }
        _ => {}
    }
}

fn subst_with_monomorphic_env(monomorphic_env: MonomorphEnv, ty: Type) -> Type {
    match ty {
        Type::Function(args, out) => {
            let new_args = args
                .iter()
                .map(|arg| subst_with_monomorphic_env(monomorphic_env.clone(), arg.clone()))
                .collect();
            let new_out = subst_with_monomorphic_env(monomorphic_env, *out);
            Type::Function(new_args, Box::new(new_out))
        }
        Type::Nominal(ident, params) => {
            let new_params = params
                .iter()
                .map(|param| subst_with_monomorphic_env(monomorphic_env.clone(), param.clone()))
                .collect();
            Type::Nominal(ident, new_params)
        }
        Type::Poly(ref polyty) => {
            if let Some(monomorphic_ty) = monomorphic_env.lookup(&polyty.name.v) {
                monomorphic_ty
            } else {
                ty
            }
        }
        Type::Tuple(elems) => {
            let new_elems = elems
                .iter()
                .map(|elem| subst_with_monomorphic_env(monomorphic_env.clone(), elem.clone()))
                .collect();
            Type::Tuple(new_elems)
        }
        _ => ty,
    }
}
