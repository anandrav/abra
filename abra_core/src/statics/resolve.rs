/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{
    ArgMaybeAnnotated, AstNode, Expr, ExprKind, FileAst, Identifier, Item, ItemKind, Pat, PatKind,
    Polytype, Stmt, StmtKind, Type, TypeDefKind, TypeKind,
};
use crate::builtin::Builtin;

use super::{Declaration, Error, Namespace, StaticsContext};

pub(crate) fn scan_declarations(ctx: &mut StaticsContext, file_asts: &Vec<Rc<FileAst>>) {
    for file in file_asts {
        let name = file.name.clone();
        let namespace = gather_declarations_file(ctx, file.clone());
        ctx.global_namespace
            .namespaces
            .insert(name, namespace.into());
    }
}

fn gather_declarations_file(ctx: &mut StaticsContext, file: Rc<FileAst>) -> Namespace {
    let mut namespace = Namespace::default();

    let qualifiers = vec![file.name.clone()];
    for item in file.items.iter() {
        gather_declarations_item(
            ctx,
            &mut namespace,
            qualifiers.clone(),
            file.clone(),
            item.clone(),
        );
    }

    namespace
}

fn fullname(qualifiers: &[String], unqualified_name: &str) -> String {
    if qualifiers.is_empty() {
        return unqualified_name.to_string();
    }
    let mut fullname = String::new();
    for _ in 0..qualifiers.len() {
        fullname.push_str(&qualifiers[0]);
        fullname.push('.');
    }
    fullname.push_str(unqualified_name);
    fullname
}

fn gather_declarations_item(
    _ctx: &mut StaticsContext,
    namespace: &mut Namespace,
    qualifiers: Vec<String>,
    _file: Rc<FileAst>,
    stmt: Rc<Item>,
) {
    match &*stmt.kind {
        ItemKind::Stmt(..) => {}
        ItemKind::InterfaceDef(iface) => {
            namespace.declarations.insert(
                iface.name.v.clone(),
                Declaration::InterfaceDef(iface.clone()),
            );

            // TODO: in the near future, put interface methods in a namespace named after the interface
            // and call interface methods using the dot operator. my_struct.to_string() etc.
            // or by fully qualifying the method and writing for example ToString.to_string(my_struct)
            for (i, p) in iface.methods.iter().enumerate() {
                let method_name = p.name.v.clone();
                let method = i as u16;
                let fully_qualified_name = fullname(&qualifiers, &method_name);
                namespace.declarations.insert(
                    method_name,
                    Declaration::InterfaceMethod {
                        iface_def: iface.clone(),
                        method,
                        fully_qualified_name,
                    },
                );
            }
        }
        ItemKind::InterfaceImpl(_) => {}
        ItemKind::TypeDef(typdefkind) => match &**typdefkind {
            // TypeDefKind::Alias(_ident, _) => {
            //     // At this stage, since we're just gathering declarations,
            //     // actually resolving the alias to the final result will have to be done later.
            // }
            TypeDefKind::Enum(e) => {
                namespace
                    .declarations
                    .insert(e.name.v.clone(), Declaration::Enum(e.clone()));

                let mut enum_namespace = Namespace::new();
                for (i, v) in e.variants.iter().enumerate() {
                    let variant_name = v.ctor.v.clone();
                    let variant = i as u16;

                    enum_namespace.declarations.insert(
                        variant_name,
                        Declaration::EnumVariant {
                            enum_def: e.clone(),
                            variant,
                        },
                    );
                }

                namespace
                    .namespaces
                    .insert(e.name.v.clone(), enum_namespace.into());
            }
            TypeDefKind::Struct(s) => {
                let struct_name = s.name.v.clone();
                namespace
                    .declarations
                    .insert(struct_name, Declaration::Struct(s.clone()));
            }
        },
        ItemKind::FuncDef(f) => {
            let func_name = f.name.v.clone();
            let fully_qualified_name = fullname(&qualifiers, &func_name);
            namespace.declarations.insert(
                func_name,
                Declaration::FreeFunction(f.clone(), fully_qualified_name),
            );
        }
        ItemKind::HostFuncDecl(func_decl) => {
            let func_name = func_decl.name.v.clone();
            let fully_qualified_name = fullname(&qualifiers, &func_name);
            namespace.declarations.insert(
                func_name.clone(),
                Declaration::HostFunction(func_decl.clone(), fully_qualified_name),
            );

            _ctx.host_funcs
                .insert(func_name, _ctx.host_funcs.len() as u16);
        }
        ItemKind::ForeignFuncDecl(_func_decl) => {
            // TODO: get the lib name using the filesystem, or report error saying why we can't
            // this function -> its file
            // some file -> parent directory
            // parent directory -> child directory with same name as file
            // child directory -> Cargo.toml
            // Cargo.toml -> name of .so/dylib/dll file

            #[cfg(feature = "ffi")]
            {
                let func_name = _func_decl.name.v.clone();

                let mut path = _file.path.clone();
                let elems: Vec<_> = _file.name.split(std::path::MAIN_SEPARATOR_STR).collect();
                for _ in 0..elems.len() - 1 {
                    path = path.parent().unwrap().to_owned();
                }
                let mut package_name = path.iter().last().unwrap().to_str().unwrap().to_string();
                if package_name.ends_with(".abra") {
                    package_name = package_name[..package_name.len() - ".abra".len()].to_string();
                }

                let filename = format!(
                    "{}{}{}",
                    std::env::consts::DLL_PREFIX,
                    package_name,
                    std::env::consts::DLL_SUFFIX
                );
                let libname = _ctx._file_provider.shared_objects_dir().join(filename);

                // add libname to string constants
                let len = _ctx.string_constants.len();
                _ctx.string_constants
                    .entry(libname.to_str().unwrap().to_string())
                    .or_insert(len);

                // TODO: duplicated with code in addon.rs
                let mut symbol = "abra_ffi".to_string();
                for elem in elems {
                    symbol.push('$');
                    symbol.push_str(elem);
                }
                symbol.push('$');
                symbol.push_str(&_func_decl.name.v);

                // add symbol to string constants
                let len = _ctx.string_constants.len();
                _ctx.string_constants.entry(symbol.clone()).or_insert(len);

                // add symbol to statics ctx
                let funcs = _ctx.dylib_to_funcs.entry(libname.clone()).or_default();
                funcs.insert(symbol.clone());

                namespace.declarations.insert(
                    func_name,
                    Declaration::_ForeignFunction {
                        decl: _func_decl.clone(),
                        libname,
                        symbol,
                    },
                );
            }
            #[cfg(not(feature = "ffi"))]
            {
                // TODO: error message if foreign function found with no ffi enabled
                todo!("ffi not enabled, can't use foreign funcs");
            }
        }
        ItemKind::Import(..) => {}
    }
}

// Map identifiers to (1) declarations and (2) namespaces
// and supports nested scopes
#[derive(Clone, Debug)]
struct SymbolTable {
    base: Rc<RefCell<SymbolTableBase>>,
}

#[derive(Default, Debug, Clone)]
struct SymbolTableBase {
    declarations: HashMap<String, Declaration>,
    namespaces: HashMap<String, Rc<Namespace>>,
    enclosing: Option<Rc<RefCell<SymbolTableBase>>>,
}

impl SymbolTableBase {
    fn lookup_declaration(&self, id: &String) -> Option<Declaration> {
        match self.declarations.get(id) {
            Some(item) => Some(item.clone()),
            None => match &self.enclosing {
                Some(enclosing) => enclosing.borrow().lookup_declaration(id),
                None => None,
            },
        }
    }

    fn lookup_namespace(&self, id: &String) -> Option<Rc<Namespace>> {
        match self.namespaces.get(id) {
            Some(ns) => Some(ns.clone()),
            None => match &self.enclosing {
                Some(enclosing) => enclosing.borrow().lookup_namespace(id),
                None => None,
            },
        }
    }

    fn extend_declaration(&mut self, id: String, decl: Declaration) {
        self.declarations.insert(id, decl);
    }

    fn extend_namespace(&mut self, id: String, ns: Rc<Namespace>) {
        self.namespaces.insert(id, ns);
    }
}

impl SymbolTable {
    pub(crate) fn empty() -> Self {
        Self {
            base: Rc::new(RefCell::new(SymbolTableBase::default())),
        }
    }

    pub(crate) fn new_scope(&self) -> Self {
        Self {
            base: Rc::new(RefCell::new(SymbolTableBase {
                enclosing: Some(self.base.clone()),
                ..Default::default()
            })),
        }
    }

    pub(crate) fn lookup_declaration(&self, id: &String) -> Option<Declaration> {
        self.base.borrow().lookup_declaration(id)
    }

    pub(crate) fn lookup_namespace(&self, id: &String) -> Option<Rc<Namespace>> {
        self.base.borrow().lookup_namespace(id)
    }

    pub(crate) fn extend_declaration(&self, id: String, decl: Declaration) {
        self.base.borrow_mut().extend_declaration(id, decl);
    }

    pub(crate) fn extend_namespace(&self, id: String, ns: Rc<Namespace>) {
        self.base.borrow_mut().extend_namespace(id, ns);
    }
}

pub(crate) fn resolve(ctx: &mut StaticsContext, file_asts: &Vec<Rc<FileAst>>) {
    for file in file_asts {
        let toplevel_declarations = resolve_imports_file(ctx, file.clone());
        let symbol_table = SymbolTable::empty();

        for (name, declaration) in toplevel_declarations.declarations {
            symbol_table.extend_declaration(name, declaration);
        }
        for (name, namespace) in toplevel_declarations.namespaces {
            symbol_table.extend_namespace(name, namespace);
        }

        for builtin in Builtin::enumerate().iter() {
            symbol_table.extend_declaration(builtin.name(), Declaration::Builtin(*builtin));
        }

        for item in file.items.iter() {
            resolve_names_item_decl(ctx, symbol_table.clone(), item.clone());
        }
        for item in file.items.iter() {
            resolve_names_item_stmt(ctx, symbol_table.clone(), item.clone());
        }
    }
}

fn resolve_imports_file(ctx: &mut StaticsContext, file: Rc<FileAst>) -> Namespace {
    // Return an environment with all identifiers available to this file.
    // That includes identifiers from this file and all imports.
    let mut env = Namespace::new();
    // add declarations from this file to the environment
    for (name, declaration) in ctx
        .global_namespace
        .namespaces
        .get(&file.name)
        .unwrap()
        .declarations
        .iter()
    {
        env.declarations.insert(name.clone(), declaration.clone());
    }
    // add child namespaces from this file to the environment
    for (name, namespace) in ctx
        .global_namespace
        .namespaces
        .get(&file.name)
        .unwrap()
        .namespaces
        .iter()
    {
        env.namespaces.insert(name.clone(), namespace.clone());
    }

    // add declarations from prelude to the environment
    for (name, declaration) in ctx
        .global_namespace
        .namespaces
        .get("prelude")
        .unwrap()
        .declarations
        .iter()
    {
        env.declarations.insert(name.clone(), declaration.clone());
    }
    // add child namespaces from prelude to the environment
    for (name, namespace) in ctx
        .global_namespace
        .namespaces
        .get("prelude")
        .unwrap()
        .namespaces
        .iter()
    {
        env.namespaces.insert(name.clone(), namespace.clone());
    }
    // builtin array type
    env.declarations
        .insert("array".to_string(), Declaration::Array);

    for item in file.items.iter() {
        if let ItemKind::Import(path) = &*item.kind {
            let Some(import_src) = ctx.global_namespace.namespaces.get(&path.v) else {
                ctx.errors
                    .push(Error::UnresolvedIdentifier { node: item.node() });
                continue;
            };
            // add declarations from this import to the environment
            for (name, declaration) in import_src.declarations.iter() {
                env.declarations.insert(name.clone(), declaration.clone());
            }
            // add child namespaces from this import to the environment
            for (name, namespace) in import_src.namespaces.iter() {
                env.namespaces.insert(name.clone(), namespace.clone());
            }
        }
    }

    env
}

fn resolve_names_item_decl(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::FuncDef(f) => {
            // TODO: Is this actually necessary? Looking up and then inserting...
            if let Some(decl @ Declaration::FreeFunction(_, _)) =
                symbol_table.lookup_declaration(&f.name.v)
            {
                ctx.resolution_map.insert(f.name.id, decl.clone());
            }
            let symbol_table = symbol_table.new_scope();
            resolve_names_func_helper(ctx, symbol_table.clone(), &f.args, &f.body, &f.ret_type);
        }
        ItemKind::HostFuncDecl(f) => {
            // TODO: Is this actually necessary? Looking up and then inserting...
            if let Some(decl @ Declaration::HostFunction { .. }) =
                symbol_table.lookup_declaration(&f.name.v)
            {
                ctx.resolution_map.insert(f.name.id, decl.clone());
            }
            let symbol_table = symbol_table.new_scope();
            for arg in &f.args {
                resolve_names_fn_arg(symbol_table.clone(), &arg.0);
                // if let Some(ty_annot) = &arg.1 {
                resolve_names_typ(ctx, symbol_table.clone(), arg.1.clone(), true);
                // }
            }

            resolve_names_typ(ctx, symbol_table.clone(), f.ret_type.clone(), true);
        }
        ItemKind::ForeignFuncDecl(f) => {
            // TODO: code almost entirely duplicated with above
            // TODO: Is this actually necessary? Looking up and then inserting...
            if let Some(decl @ Declaration::_ForeignFunction { .. }) =
                symbol_table.lookup_declaration(&f.name.v)
            {
                ctx.resolution_map.insert(f.name.id, decl.clone());
            }
            let symbol_table = symbol_table.new_scope();
            for arg in &f.args {
                resolve_names_fn_arg(symbol_table.clone(), &arg.0);
                // if let Some(ty_annot) = &arg.1 {
                resolve_names_typ(ctx, symbol_table.clone(), arg.1.clone(), true);
                // }
            }

            resolve_names_typ(ctx, symbol_table.clone(), f.ret_type.clone(), true);
        }
        ItemKind::InterfaceDef(iface_def) => {
            for prop in &iface_def.methods {
                let symbol_table = symbol_table.new_scope();
                resolve_names_typ(ctx, symbol_table.clone(), prop.ty.clone(), true);
            }
        }
        ItemKind::InterfaceImpl(iface_impl) => {
            let symbol_table = symbol_table.new_scope();
            resolve_names_typ(ctx, symbol_table.clone(), iface_impl.typ.clone(), true);
            if let Some(decl @ Declaration::InterfaceDef(_)) =
                &symbol_table.lookup_declaration(&iface_impl.iface.v)
            {
                ctx.resolution_map.insert(iface_impl.iface.id, decl.clone());
                for f in &iface_impl.methods {
                    if let Some(decl @ Declaration::InterfaceMethod { .. }) =
                        symbol_table.lookup_declaration(&f.name.v)
                    {
                        ctx.resolution_map.insert(f.name.id, decl.clone());
                    }
                    let symbol_table = symbol_table.new_scope();
                    for arg in &f.args {
                        resolve_names_fn_arg(symbol_table.clone(), &arg.0);
                        if let Some(annot) = &arg.1 {
                            resolve_names_typ(ctx, symbol_table.clone(), annot.clone(), true);
                        }
                    }
                    resolve_names_expr(ctx, symbol_table.clone(), f.body.clone());
                    if let Some(ret_type) = &f.ret_type {
                        resolve_names_typ(ctx, symbol_table, ret_type.clone(), true);
                    }
                }
            } else {
                ctx.errors
                    .push(Error::UnresolvedIdentifier { node: stmt.node() });
            }
        }
        ItemKind::Import(..) => {}
        ItemKind::TypeDef(tydef) => match &**tydef {
            TypeDefKind::Enum(enum_def) => {
                let symbol_table = symbol_table.new_scope();
                for ty_arg in &enum_def.ty_args {
                    resolve_names_polytyp(ctx, symbol_table.clone(), ty_arg.clone(), true);
                }
                for variant in &enum_def.variants {
                    if let Some(associated_data_ty) = &variant.data {
                        resolve_names_typ(
                            ctx,
                            symbol_table.clone(),
                            associated_data_ty.clone(),
                            false,
                        );
                    }
                }
            }
            TypeDefKind::Struct(struct_def) => {
                let symbol_table = symbol_table.new_scope();
                for ty_arg in &struct_def.ty_args {
                    resolve_names_polytyp(ctx, symbol_table.clone(), ty_arg.clone(), true);
                }
                for field in &struct_def.fields {
                    resolve_names_typ(ctx, symbol_table.clone(), field.ty.clone(), false);
                }
            }
        },
        ItemKind::Stmt(..) => {}
    }
}

fn resolve_names_item_stmt(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::FuncDef(..)
        | ItemKind::HostFuncDecl(..)
        | ItemKind::ForeignFuncDecl(..)
        | ItemKind::InterfaceDef(..)
        | ItemKind::InterfaceImpl(..)
        | ItemKind::Import(..)
        | ItemKind::TypeDef(..) => {}
        ItemKind::Stmt(stmt) => {
            resolve_names_stmt(ctx, symbol_table, stmt.clone());
        }
    }
}

fn resolve_names_stmt(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Stmt>) {
    match &*stmt.kind {
        StmtKind::Expr(expr) => {
            resolve_names_expr(ctx, symbol_table, expr.clone());
        }
        StmtKind::Let(_mutable, (pat, ty), expr) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());

            resolve_names_pat(ctx, symbol_table.clone(), pat.clone());
            if let Some(ty_annot) = &ty {
                resolve_names_typ(ctx, symbol_table.clone(), ty_annot.clone(), false);
            }
        }
        StmtKind::Set(lhs, rhs) => {
            resolve_names_expr(ctx, symbol_table.clone(), lhs.clone());
            resolve_names_expr(ctx, symbol_table.clone(), rhs.clone());
        }
        StmtKind::Continue | StmtKind::Break => {}
        StmtKind::Return(expr) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
        }
    }
}

fn resolve_names_expr(ctx: &mut StaticsContext, symbol_table: SymbolTable, expr: Rc<Expr>) {
    match &*expr.kind {
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_) => {}
        ExprKind::List(exprs) => {
            for expr in exprs {
                resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            }
        }
        ExprKind::Array(exprs) => {
            for expr in exprs {
                resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            }
        }
        ExprKind::Variable(symbol) => {
            let lookup = symbol_table.lookup_declaration(symbol);
            if let Some(decl) = lookup {
                ctx.resolution_map.insert(expr.id, decl);
            } else {
                ctx.errors
                    .push(Error::UnresolvedIdentifier { node: expr.node() });
            }
        }
        ExprKind::BinOp(left, _, right) => {
            resolve_names_expr(ctx, symbol_table.clone(), left.clone());
            resolve_names_expr(ctx, symbol_table, right.clone());
        }
        ExprKind::Block(statements) => {
            let symbol_table = symbol_table.new_scope();
            for statement in statements.iter() {
                resolve_names_stmt(ctx, symbol_table.clone(), statement.clone());
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            resolve_names_expr(ctx, symbol_table.clone(), cond.clone());
            resolve_names_expr(ctx, symbol_table.clone(), expr1.clone());
            if let Some(expr2) = expr2 {
                resolve_names_expr(ctx, symbol_table.clone(), expr2.clone());
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            resolve_names_expr(ctx, symbol_table.clone(), cond.clone());
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
        }
        ExprKind::Match(scrut, arms) => {
            resolve_names_expr(ctx, symbol_table.clone(), scrut.clone());
            for arm in arms {
                let symbol_table = symbol_table.new_scope();
                resolve_names_pat(ctx, symbol_table.clone(), arm.pat.clone());
                resolve_names_expr(ctx, symbol_table.clone(), arm.expr.clone());
            }
        }
        ExprKind::AnonymousFunction(args, out_ty, body) => {
            let symbol_table = SymbolTable::empty();
            resolve_names_func_helper(ctx, symbol_table.clone(), args, body, out_ty);
        }
        ExprKind::FuncAp(func, args) => {
            resolve_names_expr(ctx, symbol_table.clone(), func.clone());
            for arg in args {
                resolve_names_expr(ctx, symbol_table.clone(), arg.clone());
            }
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs {
                resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            }
        }
        ExprKind::MemberAccess(expr, field) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            if let Some(decl) = ctx.resolution_map.get(&expr.id).cloned() {
                match decl {
                    Declaration::FreeFunction(..)
                    | Declaration::HostFunction(..)
                    | Declaration::_ForeignFunction { .. }
                    | Declaration::InterfaceMethod { .. }
                    | Declaration::EnumVariant { .. }
                    | Declaration::Polytype(_)
                    | Declaration::Builtin(_)
                    | Declaration::Struct(_)
                    | Declaration::Array => {
                        ctx.errors
                            .push(Error::UnresolvedIdentifier { node: field.node() });
                    }
                    Declaration::InterfaceDef(_) => unimplemented!(),
                    Declaration::Enum(enum_def) => {
                        let mut found = false;
                        for (idx, variant) in enum_def.variants.iter().enumerate() {
                            if variant.ctor.v == field.v {
                                let enum_def = enum_def.clone();
                                ctx.resolution_map.insert(
                                    field.id,
                                    Declaration::EnumVariant {
                                        enum_def,
                                        variant: idx as u16,
                                    },
                                );
                                found = true;
                            }
                        }
                        if !found {
                            ctx.errors
                                .push(Error::UnresolvedIdentifier { node: field.node() });
                        }
                    }
                    Declaration::Var(_) => {
                        // requires further context from typechecker to resolve field
                        //
                        // for instance, if type of this Var is determined to be some struct, we can
                        // attempt to resolve the field of this member access to one of the fields in the
                        // struct's definition
                    }
                }
            }
        }
        ExprKind::MemberAccessInferred(_ident) => {
            // requires further context from typechecker to resolve field
            //
            // for instance, if type of this Var is determined to be some struct, we can
            // attempt to resolve the field of this member access to one of the fields in the
            // struct's definition
        }
        ExprKind::IndexAccess(accessed, index) => {
            resolve_names_expr(ctx, symbol_table.clone(), accessed.clone());
            resolve_names_expr(ctx, symbol_table.clone(), index.clone());
        }
    }
}

fn resolve_names_func_helper(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    args: &[ArgMaybeAnnotated],
    body: &Rc<Expr>,
    ret_type: &Option<Rc<Type>>,
) {
    for arg in args {
        resolve_names_fn_arg(symbol_table.clone(), &arg.0);
        if let Some(ty_annot) = &arg.1 {
            resolve_names_typ(ctx, symbol_table.clone(), ty_annot.clone(), true);
        }
    }

    resolve_names_expr(ctx, symbol_table.clone(), body.clone());

    if let Some(ty_annot) = ret_type {
        resolve_names_typ(ctx, symbol_table.clone(), ty_annot.clone(), true);
    }
}

fn resolve_names_fn_arg(symbol_table: SymbolTable, arg: &Rc<Identifier>) {
    symbol_table.extend_declaration(arg.v.clone(), Declaration::Var(arg.node()));
}

fn resolve_names_pat(ctx: &mut StaticsContext, symbol_table: SymbolTable, pat: Rc<Pat>) {
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Unit
        | PatKind::Int(_)
        | PatKind::Float(_)
        | PatKind::Bool(_)
        | PatKind::Str(_) => {}
        PatKind::Binding(identifier) => {
            symbol_table.extend_declaration(identifier.clone(), Declaration::Var(pat.node()));
        }
        PatKind::Variant(prefixes, tag, data) => {
            if !prefixes.is_empty() {
                let mut final_namespace: Option<Rc<Namespace>> =
                    symbol_table.lookup_namespace(&prefixes[0].v);
                for prefix in &prefixes[1..] {
                    if let Some(ns) = final_namespace {
                        final_namespace = ns.namespaces.get(&prefix.v).cloned();
                    }
                }
                let mut found = false;
                if let Some(enum_namespace) = final_namespace {
                    if let Some(ref decl @ Declaration::EnumVariant { .. }) =
                        enum_namespace.declarations.get(&tag.v).cloned()
                    {
                        found = true;
                        ctx.resolution_map.insert(tag.id, decl.clone());
                    }
                }
                if !found {
                    ctx.errors
                        .push(Error::UnresolvedIdentifier { node: tag.node() });
                }
            } else {
                // since there is no prefix to the variant, prefix must be inferred by typechecker
                // for instance,
                // let c: Color = .Red
                //                ^^^^
            }

            if let Some(data) = data {
                resolve_names_pat(ctx, symbol_table, data.clone())
            };
        }
        PatKind::Tuple(pats) => {
            for pat in pats {
                resolve_names_pat(ctx, symbol_table.clone(), pat.clone());
            }
        }
    }
}

fn resolve_names_typ(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    typ: Rc<Type>,
    introduce_poly: bool,
) {
    match &*typ.kind {
        TypeKind::Bool | TypeKind::Unit | TypeKind::Int | TypeKind::Float | TypeKind::Str => {}
        TypeKind::Poly(polyty) => {
            resolve_names_polytyp(ctx, symbol_table, polyty.clone(), introduce_poly);
        }
        TypeKind::Named(identifier) => {
            resolve_names_typ_identifier(ctx, symbol_table, identifier, typ.node());
        }
        TypeKind::NamedWithParams(identifier, args) => {
            resolve_names_typ_identifier(
                ctx,
                symbol_table.clone(),
                &identifier.v,
                identifier.node(),
            );
            for arg in args {
                resolve_names_typ(ctx, symbol_table.clone(), arg.clone(), introduce_poly);
            }
        }
        TypeKind::Function(args, out) => {
            for arg in args {
                resolve_names_typ(ctx, symbol_table.clone(), arg.clone(), introduce_poly);
            }
            resolve_names_typ(ctx, symbol_table.clone(), out.clone(), introduce_poly);
        }
        TypeKind::Tuple(elems) => {
            for elem in elems {
                resolve_names_typ(ctx, symbol_table.clone(), elem.clone(), introduce_poly);
            }
        }
    }
}

fn resolve_names_polytyp(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    polyty: Rc<Polytype>,
    introduce_poly: bool,
) {
    // Try to resolve the polymorphic type
    if let Some(decl @ Declaration::Polytype(_)) = &symbol_table.lookup_declaration(&polyty.name.v)
    {
        ctx.resolution_map.insert(polyty.name.id, decl.clone());
    }
    // If it hasn't been declared already, then this is a declaration
    else if introduce_poly {
        let decl = Declaration::Polytype(polyty.clone());
        symbol_table.extend_declaration(polyty.name.v.clone(), decl.clone());
        // it resolves to itself
        ctx.resolution_map.insert(polyty.name.id, decl);
    }

    for iface in &polyty.iface_names {
        if let Some(decl @ Declaration::InterfaceDef { .. }) =
            &symbol_table.lookup_declaration(&iface.v)
        {
            ctx.resolution_map.insert(iface.id, decl.clone());
        } else {
            ctx.errors
                .push(Error::UnresolvedIdentifier { node: iface.node() });
        }
    }
}

fn resolve_names_typ_identifier(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    identifier: &String,
    node: AstNode,
) {
    let lookup = symbol_table.lookup_declaration(identifier);
    match lookup {
        Some(decl @ (Declaration::Struct(_) | Declaration::Enum(_) | Declaration::Array)) => {
            ctx.resolution_map.insert(node.id(), decl);
        }
        _ => {
            ctx.errors.push(Error::UnresolvedIdentifier { node });
        }
    }
}
