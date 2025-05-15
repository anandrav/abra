/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use super::{Declaration, Error, Namespace, StaticsContext};
#[cfg(feature = "ffi")]
use crate::addons::make_foreign_func_name;
use crate::ast::{
    ArgMaybeAnnotated, AstNode, Expr, ExprKind, FileAst, Identifier, Item, ItemKind, Pat, PatKind,
    Polytype, Stmt, StmtKind, Type, TypeDefKind, TypeKind,
};
use crate::builtin::Builtin;
use std::cell::RefCell;
use std::rc::Rc;
use utils::hash::HashMap;

pub(crate) fn scan_declarations(ctx: &mut StaticsContext, file_asts: &Vec<Rc<FileAst>>) {
    for file in file_asts {
        let name = file.name.clone();
        let namespace = gather_declarations_file(ctx, file.clone());
        ctx.root_namespace.namespaces.insert(name, namespace.into());
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
    ctx: &mut StaticsContext,
    namespace: &mut Namespace,
    qualifiers: Vec<String>,
    _file: Rc<FileAst>,
    stmt: Rc<Item>,
) {
    match &*stmt.kind {
        ItemKind::Stmt(..) => {}
        ItemKind::InterfaceDef(iface) => {
            namespace.add_declaration(
                iface.name.v.clone(),
                Declaration::InterfaceDef(iface.clone()),
                ctx,
            );

            // TODO: in the near future, put interface methods in a namespace named after the interface
            // and call interface methods using the dot operator. my_struct.to_string() etc.
            // or by fully qualifying the method and writing for example ToString.to_string(my_struct)
            for (i, p) in iface.methods.iter().enumerate() {
                let method_name = p.name.v.clone();
                let method = i as u16;
                let fully_qualified_name = fullname(&qualifiers, &method_name);

                ctx.fully_qualified_names
                    .insert(p.name.id, fully_qualified_name);

                namespace.add_declaration(
                    method_name,
                    Declaration::InterfaceMethod {
                        i: iface.clone(),
                        method,
                    },
                    ctx,
                );
            }
        }
        ItemKind::InterfaceImpl(_) => {}
        ItemKind::Extension(_) => {
            // defer gathering declarations of member functions until declarations are gathered for type definitions
        }
        ItemKind::TypeDef(typdefkind) => match &**typdefkind {
            // TypeDefKind::Alias(_ident, _) => {
            //     // At this stage, since we're just gathering declarations,
            //     // actually resolving the alias to the final result will have to be done later.
            // }
            TypeDefKind::Enum(e) => {
                namespace.add_declaration(e.name.v.clone(), Declaration::Enum(e.clone()), ctx);

                let mut enum_namespace = Namespace::new();
                for (i, v) in e.variants.iter().enumerate() {
                    let variant_name = v.ctor.v.clone();
                    let variant = i as u16;

                    enum_namespace.add_declaration(
                        variant_name,
                        Declaration::EnumVariant {
                            e: e.clone(),
                            variant,
                        },
                        ctx,
                    );
                }

                namespace.add_namespace(e.name.v.clone(), enum_namespace.into(), ctx);

                let fully_qualified_name = fullname(&qualifiers, &e.name.v);
                ctx.fully_qualified_names
                    .insert(e.name.id, fully_qualified_name);
            }
            TypeDefKind::Struct(s) => {
                let struct_name = s.name.v.clone();
                namespace
                    .declarations
                    .insert(struct_name.clone(), Declaration::Struct(s.clone()));

                let fully_qualified_name = fullname(&qualifiers, &struct_name);
                ctx.fully_qualified_names
                    .insert(s.name.id, fully_qualified_name);
            }
        },
        ItemKind::FuncDef(f) => {
            let func_name = f.name.v.clone();
            let fully_qualified_name = fullname(&qualifiers, &func_name);

            ctx.fully_qualified_names
                .insert(f.name.id, fully_qualified_name);

            namespace.add_declaration(func_name, Declaration::FreeFunction(f.clone()), ctx);
        }
        ItemKind::HostFuncDecl(func_decl) => {
            let func_name = func_decl.name.v.clone();
            let fully_qualified_name = fullname(&qualifiers, &func_name);

            ctx.fully_qualified_names
                .insert(func_decl.name.id, fully_qualified_name);

            namespace.add_declaration(
                func_name.clone(),
                Declaration::HostFunction(func_decl.clone()),
                ctx,
            );

            ctx.host_funcs.insert(func_name);
        }
        ItemKind::ForeignFuncDecl(_func_decl) => {
            #[cfg(feature = "ffi")]
            {
                let func_name = _func_decl.name.v.clone();

                let mut path = _file.path.clone();
                let elems: Vec<_> = _file.name.split(std::path::MAIN_SEPARATOR_STR).collect();
                for _ in 0..elems.len() - 1 {
                    path = path.parent().unwrap().to_owned();
                }
                let mut package_name = path
                    .iter()
                    .next_back()
                    .unwrap()
                    .to_str()
                    .unwrap()
                    .to_string();
                if package_name.ends_with(".abra") {
                    package_name = package_name[..package_name.len() - ".abra".len()].to_string();
                }

                let filename = format!(
                    "{}{}{}{}",
                    std::env::consts::DLL_PREFIX,
                    "abra_module_",
                    package_name,
                    std::env::consts::DLL_SUFFIX
                );
                let libname = ctx._file_provider.shared_objects_dir().join(filename);

                // add libname to string constants
                ctx.string_constants
                    .insert(libname.to_str().unwrap().to_string());

                let symbol = make_foreign_func_name(&_func_decl.name.v, &elems);

                // add symbol to string constants
                ctx.string_constants.insert(symbol.clone());

                // add symbol to statics ctx
                let lib_id = ctx.dylibs.insert(libname.clone());
                ctx.dylib_to_funcs
                    .entry(lib_id)
                    .or_default()
                    .insert(symbol.clone());

                namespace.add_declaration(
                    func_name,
                    Declaration::_ForeignFunction {
                        f: _func_decl.clone(),
                        libname,
                        symbol,
                    },
                    ctx,
                );
            }
            #[cfg(not(feature = "ffi"))]
            {
                ctx.errors.push(Error::FfiNotEnabled(stmt.node()));
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
    fn lookup_declaration(&self, id: &str) -> Option<Declaration> {
        match self.declarations.get(id) {
            Some(item) => Some(item.clone()),
            None => match &self.enclosing {
                Some(enclosing) => enclosing.borrow().lookup_declaration(id),
                None => None,
            },
        }
    }

    fn lookup_namespace(&self, id: &str) -> Option<Rc<Namespace>> {
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

    pub(crate) fn from_namespace(namespace: Namespace) -> Self {
        let ret = Self::empty();
        for (name, declaration) in namespace.declarations {
            ret.extend_declaration(name, declaration);
        }
        for (name, namespace) in namespace.namespaces {
            ret.extend_namespace(name, namespace);
        }
        ret
    }

    pub(crate) fn new_scope(&self) -> Self {
        Self {
            base: Rc::new(RefCell::new(SymbolTableBase {
                enclosing: Some(self.base.clone()),
                ..Default::default()
            })),
        }
    }

    pub(crate) fn lookup_declaration(&self, id: &str) -> Option<Declaration> {
        self.base.borrow().lookup_declaration(id)
    }

    pub(crate) fn lookup_namespace(&self, id: &str) -> Option<Rc<Namespace>> {
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
        let symbol_table = resolve_imports_file(ctx, file.clone());

        for item in file.items.iter() {
            resolve_names_item_decl(ctx, symbol_table.clone(), item.clone());
        }
        for item in file.items.iter() {
            resolve_names_item_stmt(ctx, symbol_table.clone(), item.clone());
        }
    }
}

fn resolve_imports_file(ctx: &mut StaticsContext, file: Rc<FileAst>) -> SymbolTable {
    // Create a namespace containing all symbols available to this file
    // That includes
    // 1. symbols defined in this file
    // 2. symbols made available via import statements
    // 3. symbols that are always globally available to any file
    let mut effective_namespace = Namespace::new();

    // builtin array type
    effective_namespace
        .declarations
        .insert("array".to_string(), Declaration::Array);
    // builtin operations
    for builtin in Builtin::enumerate().iter() {
        effective_namespace
            .declarations
            .insert(builtin.name(), Declaration::Builtin(*builtin));
    }
    // always include the prelude (unless this file is the prelude)
    if file.name != "prelude" {
        effective_namespace.add_other(
            &ctx.root_namespace
                .namespaces
                .get("prelude")
                .cloned()
                .unwrap(),
            ctx,
        );
    }

    // add declarations from this file to the effective namespace
    effective_namespace.add_other(
        &ctx.root_namespace
            .namespaces
            .get(&file.name)
            .cloned()
            .unwrap(),
        ctx,
    );

    for item in file.items.iter() {
        if let ItemKind::Import(path) = &*item.kind {
            let Some(import_src) = ctx.root_namespace.namespaces.get(&path.v).cloned() else {
                ctx.errors
                    .push(Error::UnresolvedIdentifier { node: item.node() });
                continue;
            };
            effective_namespace.add_other(&import_src, ctx);
        }
    }

    SymbolTable::from_namespace(effective_namespace)
}

impl Namespace {
    // add children from another namespace to this namespace
    pub fn add_other(&mut self, other: &Self, ctx: &mut StaticsContext) {
        // child declarations
        for (name, decl) in other.declarations.iter() {
            self.add_declaration(name.clone(), decl.clone(), ctx);
        }
        // child namespaces
        for (name, namespace) in other.namespaces.iter() {
            self.add_namespace(name.clone(), namespace.clone(), ctx);
        }
    }

    pub fn add_declaration(&mut self, name: String, decl: Declaration, ctx: &mut StaticsContext) {
        use std::collections::hash_map::*;
        match self.declarations.entry(name.clone()) {
            Entry::Occupied(occ) => {
                ctx.errors.push(Error::NameClash {
                    name,
                    original: occ.get().clone(),
                    new: decl,
                });
            }
            Entry::Vacant(vac) => {
                vac.insert(decl);
            }
        }
    }

    pub fn add_namespace(
        &mut self,
        name: String,
        namespace: Rc<Namespace>,
        _ctx: &mut StaticsContext,
    ) {
        use std::collections::hash_map::*;
        match self.namespaces.entry(name.clone()) {
            Entry::Occupied(_) => {
                // ASSUMPTION: this will never happen
                // A namespace is only inserted
                // 1. for structs and enums
                //     - in this case, their declarations will conflict with each other already, so it's
                //       OK if we overwrite the namespace of one with the other. The conflict between the
                //       declarations will be detected in .add_declaration()
                // 2. for files but ONLY into the root namespace
                //     - a conflict cannot happen because two files/directories cannot be named the same thing
                panic!("duplicate key in namespaces");
            }
            Entry::Vacant(vac) => {
                vac.insert(namespace.clone());
            }
        }
    }
}

fn resolve_names_item_decl(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::FuncDef(f) => {
            resolve_identifier(ctx, &symbol_table, &f.name); // THIS IS ONLY USED TO GET THE FULLY QUALIFIED NAME THIS IS FUCKING DUMB
            let symbol_table = symbol_table.new_scope();
            resolve_names_func_helper(ctx, symbol_table.clone(), &f.args, &f.body, &f.ret_type);
        }
        ItemKind::HostFuncDecl(f) | ItemKind::ForeignFuncDecl(f) => {
            let symbol_table = symbol_table.new_scope();
            for arg in &f.args {
                resolve_names_fn_arg(symbol_table.clone(), &arg.0);
                resolve_names_typ(ctx, symbol_table.clone(), arg.1.clone(), true);
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
            resolve_identifier(ctx, &symbol_table, &iface_impl.iface);
            resolve_names_typ(ctx, symbol_table.clone(), iface_impl.typ.clone(), true);
            // TODO: there is code duplication with ItemKind::FuncDef and ItemKind::Extension
            for f in &iface_impl.methods {
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
        }
        ItemKind::Extension(ext) => {
            let symbol_table = symbol_table.new_scope();
            resolve_identifier(ctx, &symbol_table, &ext.typename);
            // TODO: there is code duplication here with ItemKind::FuncDef and ItemKind::InterfaceImpl
            for f in &ext.methods {
                ctx.fully_qualified_names
                    .insert(f.name.id, f.name.v.clone());
                // THIS IS ONLY USED TO GET THE FULLY QUALIFIED NAME THIS IS FUCKING DUMB
                // ctx.resolution_map.insert(
                //     f.name.id,
                //     Declaration::MemberFunction {
                //         f: f.clone(),
                //         name: f.name.v.clone(),
                //     },
                // );
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

            // In this pass, we also gather the declarations of member functions
            // We don't gather declarations of member functions in the same pass as gathering type definitions, because
            // the former depends on the latter
            if let Some(decl) = ctx.resolution_map.get(&ext.typename.id).cloned() {
                match decl {
                    Declaration::Struct(struct_def) => {
                        for f in &ext.methods {
                            let fully_qualified_type_name =
                                ctx.fully_qualified_names[&struct_def.name.id].clone();
                            let fully_qualified_name = fully_qualified_type_name + &f.name.v;
                            ctx.fully_qualified_names
                                .insert(f.name.id, fully_qualified_name);

                            match ctx
                                .member_functions
                                .entry(struct_def.id)
                                .or_default()
                                .entry(f.name.v.clone())
                            {
                                std::collections::hash_map::Entry::Occupied(occupied_entry) => {
                                    ctx.errors.push(Error::NameClash {
                                        name: f.name.v.clone(),
                                        original: Declaration::FreeFunction(
                                            occupied_entry.get().clone(), // gross
                                        ),
                                        new: Declaration::FreeFunction(f.clone()),
                                    })
                                }
                                std::collections::hash_map::Entry::Vacant(vacant_entry) => {
                                    vacant_entry.insert(f.clone());
                                }
                            }
                        }
                    }
                    Declaration::Enum(_) => {
                        todo!();
                    }
                    _ => ctx.errors.push(Error::MustExtendStructOrEnum {
                        node: ext.typename.node(),
                        name: ext.typename.v.clone(),
                    }),
                }
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
        | ItemKind::Extension(..)
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

fn resolve_identifier(
    ctx: &mut StaticsContext,
    symbol_table: &SymbolTable,
    ident: &Rc<Identifier>,
) {
    resolve_symbol(ctx, symbol_table, &ident.v, ident.node())
}

fn resolve_symbol(
    ctx: &mut StaticsContext,
    symbol_table: &SymbolTable,
    symbol: &str,
    node: AstNode,
) {
    if let Some(decl) = symbol_table.lookup_declaration(symbol) {
        ctx.resolution_map.insert(node.id(), decl.clone());
    } else {
        ctx.errors.push(Error::UnresolvedIdentifier { node });
    }
}

fn resolve_names_expr(ctx: &mut StaticsContext, symbol_table: SymbolTable, expr: Rc<Expr>) {
    match &*expr.kind {
        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_) => {}
        ExprKind::Array(exprs) => {
            for expr in exprs {
                resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            }
        }
        ExprKind::Variable(symbol) => {
            resolve_symbol(ctx, &symbol_table, symbol, expr.node());
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
                resolve_names_stmt(ctx, symbol_table.clone(), arm.stmt.clone());
            }
        }
        ExprKind::AnonymousFunction(args, out_ty, body) => {
            let symbol_table = SymbolTable::empty();
            resolve_names_func_helper(ctx, symbol_table.clone(), args, body, out_ty);
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs {
                resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            }
        }
        ExprKind::FuncAp(func, args) => {
            resolve_names_expr(ctx, symbol_table.clone(), func.clone());
            for arg in args {
                resolve_names_expr(ctx, symbol_table.clone(), arg.clone());
            }
        }
        ExprKind::MemberFuncAp(expr, _fname, args) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());

            // TODO: code duplicated with MemberAccess below
            if let Some(decl) = ctx.resolution_map.get(&expr.id).cloned() {
                match decl {
                    Declaration::FreeFunction(..)
                    | Declaration::HostFunction(..)
                    | Declaration::_ForeignFunction { .. }
                    | Declaration::InterfaceMethod { .. }
                    | Declaration::MemberFunction { .. }
                    | Declaration::EnumVariant { .. }
                    | Declaration::Polytype(_)
                    | Declaration::Builtin(_)
                    | Declaration::Struct(_)
                    | Declaration::Array => {
                        ctx.errors.push(Error::UnresolvedIdentifier {
                            node: _fname.node(),
                        });
                    }
                    Declaration::InterfaceDef(_) => unimplemented!(),
                    Declaration::Enum(enum_def) => {
                        let mut found = false;
                        for (idx, variant) in enum_def.variants.iter().enumerate() {
                            if variant.ctor.v == _fname.v {
                                let enum_def = enum_def.clone();
                                ctx.resolution_map.insert(
                                    _fname.id,
                                    Declaration::EnumVariant {
                                        e: enum_def,
                                        variant: idx as u16,
                                    },
                                );
                                found = true;
                            }
                        }
                        if !found {
                            ctx.errors.push(Error::UnresolvedIdentifier {
                                node: _fname.node(),
                            });
                        }
                    }
                    Declaration::Var(_) => {
                        // do nothing
                        //
                        // requires further context from typechecker to resolve field
                        //
                        // for instance, if type of this Var is determined to be some struct, we can
                        // attempt to resolve the field of this member access to one of the fields in the
                        // struct's definition
                    }
                }
            }

            for arg in args {
                resolve_names_expr(ctx, symbol_table.clone(), arg.clone());
            }
        }
        ExprKind::MemberAccess(expr, field) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());

            // TODO: code duplicated in MemberFuncAp above
            if let Some(decl) = ctx.resolution_map.get(&expr.id).cloned() {
                match decl {
                    Declaration::FreeFunction(..)
                    | Declaration::HostFunction(..)
                    | Declaration::_ForeignFunction { .. }
                    | Declaration::InterfaceMethod { .. }
                    | Declaration::MemberFunction { .. }
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
                                        e: enum_def,
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
                        // do nothing
                        //
                        // requires further context from typechecker to resolve field
                        //
                        // for instance, if type of this Var is determined to be some struct, we can
                        // attempt to resolve the field of this member access to one of the fields in the
                        // struct's definition
                    }
                }
            }
        }
        ExprKind::MemberAccessLeadingDot(_ident) => {
            // do nothing
            //
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
        ExprKind::Unwrap(expr) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
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
            resolve_symbol(ctx, &symbol_table, identifier, typ.node());
        }
        TypeKind::NamedWithParams(identifier, args) => {
            resolve_identifier(ctx, &symbol_table, identifier);
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
        resolve_identifier(ctx, &symbol_table, iface);
    }
}
