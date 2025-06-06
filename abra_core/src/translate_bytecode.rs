/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::assembly::{Instr, Label, Line, remove_labels};
use crate::ast::{AstNode, BinaryOperator, FuncDef, InterfaceDecl, ItemKind};
use crate::ast::{FileAst, FileDatabase, NodeId};
use crate::builtin::Builtin;
use crate::environment::Environment;
use crate::statics::typecheck::Nominal;
use crate::statics::typecheck::SolvedType;
use crate::statics::{Declaration, TypeProv};
use crate::statics::{Type, ty_fits_impl_ty};
use crate::vm::{AbraFloat, AbraInt, Instr as VmInstr};
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

type OffsetTable = HashMap<NodeId, i32>;
type MonomorphEnv = Environment<String, Type>;
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
struct TranslatorState {
    lines: Vec<Line>,
    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,
    function_name_arena: IdSet<String>,
    instr_count: usize,
    func_map: HashMap<FuncDesc, Label>,
    funcs_to_generate: Vec<FuncDesc>,
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

    pub(crate) fn translate(&self) -> CompiledProgram {
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
                for (offset, node_id) in locals.iter().enumerate() {
                    offset_table.entry(*node_id).or_insert((offset) as i32);
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

            while !st.funcs_to_generate.is_empty() {
                // Generate bytecode for function bodies
                let mut iteration = Vec::new();
                mem::swap(&mut (iteration), &mut st.funcs_to_generate);
                for desc in iteration {
                    if let FuncKind::NamedFunc(f) = &desc.kind {
                        self.update_function_name_table(st, &f.name.v);
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
                        update_monomorph_env(monomorph_env.clone(), func_ty, overload_ty.clone());
                    }

                    let return_label = make_label("return");

                    let label = st.func_map.get(&desc).unwrap();
                    self.emit(st, Line::Label(label.clone()));

                    let mut locals = HashSet::default();
                    collect_locals_expr(body, &mut locals);
                    let locals_count = locals.len();
                    for _ in 0..locals_count {
                        self.emit(st, Instr::PushNil);
                    }
                    let mut offset_table = OffsetTable::default();
                    for (i, arg) in args.iter().rev().enumerate() {
                        offset_table.entry(arg.0.id).or_insert(-(i as i32) - 1);
                    }
                    for (i, local) in locals.iter().enumerate() {
                        offset_table.entry(*local).or_insert((i) as i32);
                    }
                    let nargs = args.len();
                    st.return_stack.push(return_label.clone());
                    self.translate_expr(body.clone(), &offset_table, monomorph_env.clone(), st);
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
        &self,
        expr: Rc<Expr>,
        offset_table: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_filename_lineno_tables(st, expr.node());
        match &*expr.kind {
            ExprKind::Variable(_) => match &self.statics.resolution_map[&expr.id] {
                Declaration::EnumVariant { variant, .. } => {
                    self.emit(st, Instr::PushNil);
                    self.emit(st, Instr::ConstructVariant { tag: *variant });
                }
                Declaration::Var(node) => {
                    let idx = offset_table.get(&node.id()).unwrap();
                    self.emit(st, Instr::LoadOffset(*idx));
                }
                Declaration::Builtin(b) => match b {
                    Builtin::Newline => {
                        self.emit(st, Instr::PushString("\n".to_owned()));
                    }
                    _ => {
                        unimplemented!()
                    }
                },
                Declaration::FreeFunction(f) => {
                    let name = &self.statics.fully_qualified_names[&f.name.id];
                    self.emit(
                        st,
                        Instr::MakeClosure {
                            func_addr: name.clone(),
                        },
                    );
                }
                Declaration::Struct(_)
                | Declaration::_ForeignFunction { .. }
                | Declaration::HostFunction(..)
                | Declaration::InterfaceMethod { .. }
                | Declaration::MemberFunction { .. } => unimplemented!(),
                Declaration::Enum { .. } => {}

                Declaration::InterfaceDef(_) | Declaration::Array | Declaration::Polytype(_) => {
                    unreachable!()
                }
            },
            ExprKind::MemberAccessLeadingDot(ident) => match self.statics.resolution_map[&ident.id]
            {
                Declaration::EnumVariant { variant, .. } => {
                    self.emit(st, Instr::PushNil);
                    self.emit(st, Instr::ConstructVariant { tag: variant });
                }
                _ => panic!(),
            },
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
                let mut helper = |monomorph_env, method_name: &str| {
                    let iface_method = self
                        .statics
                        .root_namespace
                        .get_declaration(method_name)
                        .unwrap();
                    let Declaration::InterfaceMethod {
                        method,
                        i: iface_def,
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
                        iface_def,
                        method,
                        func_ty,
                    );
                };
                match op {
                    BinaryOperator::Add => helper(monomorph_env, "prelude.add"),
                    BinaryOperator::Subtract => helper(monomorph_env, "prelude.subtract"),
                    BinaryOperator::Multiply => helper(monomorph_env, "prelude.multiply"),
                    BinaryOperator::Divide => helper(monomorph_env, "prelude.divide"),
                    BinaryOperator::GreaterThan => helper(monomorph_env, "prelude.greater_than"),
                    BinaryOperator::LessThan => helper(monomorph_env, "prelude.less_than"),
                    BinaryOperator::GreaterThanOrEqual => {
                        helper(monomorph_env, "prelude.greater_than_or_equal")
                    }
                    BinaryOperator::LessThanOrEqual => {
                        helper(monomorph_env, "prelude.less_than_or_equal")
                    }
                    BinaryOperator::Equal => {
                        helper(monomorph_env, "prelude.equal");
                    }
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

                        let arg1_ty = self.statics.solution_of_node(left.node()).unwrap();
                        let arg2_ty = self.statics.solution_of_node(right.node()).unwrap();
                        let out_ty = self.statics.solution_of_node(expr.node()).unwrap();
                        let specific_func_ty =
                            Type::Function(vec![arg1_ty, arg2_ty], out_ty.into());

                        let substituted_ty =
                            subst_with_monomorphic_env(monomorph_env, specific_func_ty);

                        self.handle_func_call(st, Some(substituted_ty), func_name, func.clone());
                    }
                    BinaryOperator::Or => self.emit(st, Instr::Or),
                    BinaryOperator::And => self.emit(st, Instr::And),
                    BinaryOperator::Pow => helper(monomorph_env, "prelude.power"),
                    BinaryOperator::Mod => self.emit(st, Instr::Modulo),
                }
            }
            ExprKind::MemberFuncAp(expr, fname, args) => {
                self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                for arg in args {
                    self.translate_expr(arg.clone(), offset_table, monomorph_env.clone(), st);
                }

                let resolution = &self.statics.resolution_map[&fname.id];
                self.translate_func_ap(
                    resolution.clone(),
                    fname.node(),
                    offset_table,
                    monomorph_env,
                    st,
                );
            }
            ExprKind::FuncAp(func, args) => {
                for arg in args {
                    self.translate_expr(arg.clone(), offset_table, monomorph_env.clone(), st);
                }
                let resolution = match &*func.kind {
                    ExprKind::Variable(_) => &self.statics.resolution_map[&func.id],
                    ExprKind::MemberAccess(_prefix, ident) => {
                        &self.statics.resolution_map[&ident.id]
                    }
                    ExprKind::MemberAccessLeadingDot(..) => unimplemented!(),

                    ExprKind::Unit
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

                self.translate_func_ap(
                    resolution.clone(),
                    func.node(),
                    offset_table,
                    monomorph_env,
                    st,
                );
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
                if statements.is_empty() {
                    self.emit(st, Instr::PushNil);
                }
            }
            ExprKind::Tuple(exprs) => {
                for expr in exprs {
                    self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                }
                self.emit(st, Instr::Construct(exprs.len() as u16));
            }
            ExprKind::IfElse(cond, then_block, else_block) => {
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
            ExprKind::MemberAccess(accessed, field_name) => {
                if let Some(Declaration::EnumVariant { variant, .. }) =
                    &self.statics.resolution_map.get(&field_name.id)
                {
                    self.emit(st, Instr::PushNil);
                    self.emit(st, Instr::ConstructVariant { tag: *variant });
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

                    self.translate_stmt(
                        arm.stmt.clone(),
                        true,
                        offset_table,
                        monomorph_env.clone(),
                        st,
                    );
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
                    let substituted_ty = subst_with_monomorphic_env(monomorph_env, func_ty);
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
                self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);

                // check if yes or no
                self.emit(st, Instr::Deconstruct);
                self.emit(st, Instr::PushInt(1));
                self.emit(st, Instr::Equal);

                // if no, panic
                // if yes, inner value
                let no_label = make_label("no");
                let yes_label = make_label("endif");
                self.emit(st, Instr::JumpIf(no_label.clone()));
                self.emit(st, Instr::Jump(yes_label.clone()));
                self.emit(st, Line::Label(no_label));
                self.emit(st, Instr::Panic);
                self.emit(st, Line::Label(yes_label));
            }
        }
    }

    // used for free functions and member functions
    fn translate_func_ap_helper(
        &self,
        f: &Rc<FuncDef>,
        f_fully_qualified_name: &String,
        func_node: AstNode,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        let func_ty = self.statics.solution_of_node(f.name.node()).unwrap();
        if !func_ty.is_overloaded() {
            self.handle_func_call(st, None, f_fully_qualified_name, f.clone());
        } else {
            let specific_func_ty = self.statics.solution_of_node(func_node).unwrap();
            let substituted_ty = subst_with_monomorphic_env(monomorph_env, specific_func_ty);
            self.handle_func_call(st, Some(substituted_ty), f_fully_qualified_name, f.clone());
        }
    }

    // used for interface methods
    fn translate_iface_method_ap_helper(
        &self,
        st: &mut TranslatorState,
        monomorph_env: MonomorphEnv,
        iface_def: Rc<InterfaceDecl>,
        method: u16,
        func_ty: SolvedType,
    ) {
        let substituted_ty = subst_with_monomorphic_env(monomorph_env.clone(), func_ty);
        let method = &iface_def.methods[method as usize].name;
        let impl_list = self.statics.interface_impls[&iface_def].clone();

        for imp in impl_list {
            for f in &imp.methods {
                if f.name.v == *method.v {
                    let unifvar = self
                        .statics
                        .unifvars
                        .get(&TypeProv::Node(f.name.node()))
                        .unwrap();
                    let interface_impl_ty = unifvar.solution().unwrap();

                    if ty_fits_impl_ty(&self.statics, substituted_ty.clone(), interface_impl_ty) {
                        let fully_qualified_name = &self.statics.fully_qualified_names[&method.id];
                        self.handle_func_call(
                            st,
                            Some(substituted_ty.clone()),
                            fully_qualified_name,
                            f.clone(),
                        );
                    }
                }
            }
        }
    }

    fn translate_func_ap(
        &self,
        resolution: Declaration,
        func_node: AstNode,
        offset_table: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        match &resolution {
            Declaration::Var(node) => {
                // assume it's a function object
                let idx = offset_table.get(&node.id()).unwrap();
                self.emit(st, Instr::LoadOffset(*idx));
                self.emit(st, Instr::CallFuncObj);
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
                let idx = self.statics.host_funcs.get_id(&decl.name.v) as u16;
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
                self.emit(st, Instr::CallExtern(func_id));
            }
            Declaration::InterfaceMethod {
                i: iface_def,
                method,
            } => {
                let func_ty = self.statics.solution_of_node(func_node).unwrap();
                self.translate_iface_method_ap_helper(
                    st,
                    monomorph_env,
                    iface_def.clone(),
                    *method,
                    func_ty,
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
                self.emit(st, Instr::Construct(def.fields.len() as u16));
            }
            Declaration::EnumVariant {
                e: enum_def,
                variant,
            } => {
                let arity = enum_def.arity(*variant);
                if arity > 1 {
                    // turn the arguments (associated data) into a tuple
                    self.emit(st, Instr::Construct(arity));
                }
                self.emit(st, Instr::ConstructVariant { tag: *variant });
            }
            Declaration::Enum { .. } => {
                panic!("can't call enum name as ctor");
            }
            Declaration::Builtin(b) => match b {
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
                Builtin::ArrayPush => {
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
            Declaration::InterfaceDef(_) | Declaration::Array | Declaration::Polytype(_) => {
                unreachable!()
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
                    let Declaration::EnumVariant { variant, .. } =
                        &self.statics.resolution_map[&ctor.id]
                    else {
                        panic!("expected variable to be defined in node");
                    };
                    let tag_fail_label = make_label("tag_fail");
                    let end_label = make_label("endvariant");

                    self.emit(st, Instr::Deconstruct);
                    self.emit(st, Instr::PushInt(*variant as AbraInt));
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

    fn translate_stmt(
        &self,
        stmt: Rc<Stmt>,
        is_last: bool,
        offset_table: &OffsetTable,
        monomorph_env: MonomorphEnv,
        st: &mut TranslatorState,
    ) {
        self.update_filename_lineno_tables(st, stmt.node());
        match &*stmt.kind {
            StmtKind::Let(_, pat, expr) => {
                self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                self.handle_pat_binding(pat.0.clone(), offset_table, st);

                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::Set(expr1, rvalue) => {
                match &*expr1.kind {
                    ExprKind::Variable(_) => {
                        let Declaration::Var(node) = &self.statics.resolution_map[&expr1.id] else {
                            panic!("expected variableto be defined in node");
                        };
                        let idx = offset_table.get(&node.id()).unwrap();
                        self.translate_expr(
                            rvalue.clone(),
                            offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                        self.emit(st, Instr::StoreOffset(*idx));
                    }
                    ExprKind::MemberAccess(accessed, field_name) => {
                        self.translate_expr(
                            rvalue.clone(),
                            offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                        self.translate_expr(
                            accessed.clone(),
                            offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                        let idx = idx_of_field(&self.statics, accessed.clone(), &field_name.v);
                        self.emit(st, Instr::SetField(idx));
                    }
                    ExprKind::IndexAccess(array, index) => {
                        self.translate_expr(
                            rvalue.clone(),
                            offset_table,
                            monomorph_env.clone(),
                            st,
                        );
                        self.translate_expr(index.clone(), offset_table, monomorph_env.clone(), st);
                        self.translate_expr(array.clone(), offset_table, monomorph_env.clone(), st);
                        self.emit(st, Instr::SetIdx);
                    }
                    _ => unimplemented!(),
                }
                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::Expr(expr) => {
                self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                if !is_last {
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
                self.translate_expr(expr.clone(), offset_table, monomorph_env.clone(), st);
                let return_label = st.return_stack.last().unwrap();
                self.emit(st, Instr::Jump(return_label.clone()));
            }
            StmtKind::If(cond, then_block) => {
                self.translate_expr(cond.clone(), offset_table, monomorph_env.clone(), st);
                let then_label = make_label("then");
                let end_label = make_label("endif");
                self.emit(st, Instr::JumpIf(then_label.clone()));
                self.emit(st, Instr::Jump(end_label.clone()));
                self.emit(st, Line::Label(then_label));
                self.translate_expr(then_block.clone(), offset_table, monomorph_env.clone(), st);
                self.emit(st, Instr::Pop);
                self.emit(st, Line::Label(end_label));

                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
            StmtKind::WhileLoop(cond, body) => {
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

                if is_last {
                    self.emit(st, Instr::PushNil);
                }
            }
        }
    }

    fn handle_func_call(
        &self,
        st: &mut TranslatorState,
        overload_ty: Option<Type>,
        func_name: &String,
        func_def: Rc<FuncDef>,
    ) {
        let desc = FuncDesc {
            kind: FuncKind::NamedFunc(func_def.clone()),
            overload_ty: overload_ty.clone(),
        };
        let label = self.get_func_label(st, desc, overload_ty, func_name);
        self.emit(st, Instr::Call(label));
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
                        let monoty = overload_ty.monotype().unwrap();
                        let mut label_hint = format!("{}__{}", func_name, monoty);
                        label_hint.retain(|c| !c.is_whitespace());
                        make_label(&label_hint)
                    }
                };
                v.insert(label.clone());
                label
            }
        }
    }

    fn handle_pat_binding(&self, pat: Rc<Pat>, locals: &OffsetTable, st: &mut TranslatorState) {
        match &*pat.kind {
            PatKind::Binding(_) => {
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
                collect_locals_stmt(&[arm.stmt.clone()], locals);
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
            collect_locals_expr(expr, locals);
            for arg in args {
                collect_locals_expr(arg, locals);
            }
        }
        ExprKind::AnonymousFunction(..)
        | ExprKind::MemberAccessLeadingDot(..)
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
            StmtKind::Let(_, pat, expr) => {
                collect_locals_pat(pat.0.clone(), locals);
                collect_locals_expr(expr, locals);
            }
            StmtKind::Set(..) | StmtKind::Continue | StmtKind::Break => {}
            StmtKind::Return(expr) => {
                collect_locals_expr(expr, locals);
            }
            StmtKind::If(cond, body) => {
                collect_locals_expr(cond, locals);
                collect_locals_expr(body, locals);
            }
            StmtKind::WhileLoop(cond, body) => {
                collect_locals_expr(cond, locals);
                collect_locals_expr(body, locals);
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
