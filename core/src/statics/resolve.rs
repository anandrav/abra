use std::cell::RefCell;
use std::collections::BTreeMap;
use std::rc::Rc;

use crate::ast::{
    ArgAnnotated, Expr, ExprKind, FileAst, Item, ItemKind, Node, NodeId, Pat, PatKind, Stmt,
    StmtKind, Type, TypeDefKind, TypeKind,
};
use crate::builtin::Builtin;

use super::{Declaration, Namespace, StaticsContext};

pub(crate) fn scan_declarations(ctx: &mut StaticsContext, files: Vec<Rc<FileAst>>) {
    for file in files {
        let name = file.name.clone();
        let namespace = gather_declarations_file(file.clone());
        ctx.global_namespace
            .namespaces
            .insert(name, namespace.into());
    }
}

fn gather_declarations_file(file: Rc<FileAst>) -> Namespace {
    let mut namespace = Namespace::default();

    let qualifiers = vec![file.name.clone()];
    for item in file.items.iter() {
        gather_declarations_item(&mut namespace, qualifiers.clone(), item.clone());
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

fn gather_declarations_item(namespace: &mut Namespace, qualifiers: Vec<String>, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::Stmt(..) => {}
        ItemKind::InterfaceDef(iface) => {
            namespace.declarations.insert(
                iface.name.v.clone(),
                Declaration::InterfaceDef(iface.clone()),
            );

            // TODO: in the near future, put interface methods in a namespace named after the interface
            // and call interface methods using the dot operator. my_struct.to_string() etc.
            for (i, p) in iface.props.iter().enumerate() {
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

                // TODO: in the near future, put enum variants in a namespace named after the enum
                // and refer to them in code by just writing .Variant
                for (i, v) in e.variants.iter().enumerate() {
                    let variant_name = v.ctor.v.clone();
                    let variant = i as u16;

                    namespace.declarations.insert(
                        variant_name,
                        Declaration::EnumVariant {
                            enum_def: e.clone(),
                            variant,
                        },
                    );
                }
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
    declarations: BTreeMap<String, Declaration>,
    //namespaces: BTreeMap<String, Rc<Namespace>>,
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

    // fn lookup_namespace(&self, id: &String) -> Option<Rc<Namespace>> {
    //     match self.namespaces.get(id) {
    //         Some(ns) => Some(ns.clone()),
    //         None => match &self.enclosing {
    //             Some(enclosing) => enclosing.borrow().lookup_namespace(id),
    //             None => None,
    //         },
    //     }
    // }

    fn extend_declaration(&mut self, id: String, decl: Declaration) {
        self.declarations.insert(id, decl);
    }

    // fn extend_namespace(&mut self, id: String, ns: Rc<Namespace>) {
    //     self.namespaces.insert(id, ns);
    // }
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

    // pub(crate) fn lookup_namespace(&self, id: &String) -> Option<Rc<Namespace>> {
    //     self.base.borrow().lookup_namespace(id)
    // }

    pub(crate) fn extend_declaration(&self, id: String, decl: Declaration) {
        self.base.borrow_mut().extend_declaration(id, decl);
    }

    // pub(crate) fn extend_namespace(&self, id: String, ns: Rc<Namespace>) {
    //     self.base.borrow_mut().extend_namespace(id, ns);
    // }
}

// TODO: make a custom type to detect collisions
pub type ToplevelDeclarations = BTreeMap<String, Declaration>;

pub(crate) fn resolve(ctx: &mut StaticsContext, files: Vec<Rc<FileAst>>) {
    for file in files {
        let env = resolve_imports_file(ctx, file.clone());
        resolve_names_file(ctx, env.clone(), file.clone());
    }
}

fn resolve_imports_file(ctx: &mut StaticsContext, file: Rc<FileAst>) -> ToplevelDeclarations {
    // Return an environment with all identifiers available to this file.
    // That includes identifiers from this file and all imports.
    let mut env = ToplevelDeclarations::new();
    // add declarations from this file to the environment
    for (name, declaration) in ctx
        .global_namespace
        .namespaces
        .get(&file.name)
        .unwrap()
        .declarations
        .iter()
    {
        env.insert(name.clone(), declaration.clone());
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
        env.insert(name.clone(), declaration.clone());
    }
    // builtin array type
    env.insert("array".to_string(), Declaration::Array);

    for item in file.items.iter() {
        if let ItemKind::Import(path) = &*item.kind {
            // add declarations from this import to the environment
            for (name, declaration) in ctx
                .global_namespace
                .namespaces
                .get(&path.v)
                .unwrap()
                .declarations
                .iter()
            {
                env.insert(name.clone(), declaration.clone());
            }
        }
    }

    env
}

pub(crate) fn resolve_names_file(
    ctx: &mut StaticsContext,
    toplevel_declarations: ToplevelDeclarations,
    file: Rc<FileAst>,
) {
    let symbol_table = SymbolTable::empty();

    for (name, declaration) in toplevel_declarations {
        symbol_table.extend_declaration(name, declaration);
    }

    for (i, eff) in ctx.effects.iter().enumerate() {
        symbol_table.extend_declaration(eff.name.clone(), Declaration::Effect(i as u16));
    }
    for builtin in Builtin::enumerate().iter() {
        symbol_table.extend_declaration(builtin.name(), Declaration::Builtin(*builtin));
    }
    for item in file.items.iter() {
        resolve_names_item(ctx, symbol_table.clone(), item.clone());
    }
}

fn resolve_names_item(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::FuncDef(f) => {
            if let Some(decl @ Declaration::FreeFunction(_, _)) =
                symbol_table.lookup_declaration(&f.name.v)
            {
                ctx.resolution_map.insert(f.name.id, decl.clone());
            }
            let symbol_table = symbol_table.new_scope();
            for arg in &f.args {
                resolve_names_pat(ctx, symbol_table.clone(), arg.0.clone());
                if let Some(annot) = &arg.1 {
                    resolve_names_typ(ctx, symbol_table.clone(), annot.clone());
                }
            }
            resolve_names_expr(ctx, symbol_table.clone(), f.body.clone());
            if let Some(ret_type) = &f.ret_type {
                resolve_names_typ(ctx, symbol_table, ret_type.clone());
            }
        }
        ItemKind::InterfaceDef(iface_def) => {
            for prop in &iface_def.props {
                resolve_names_typ(ctx, symbol_table.clone(), prop.ty.clone());
            }
        }
        ItemKind::InterfaceImpl(iface_impl) => {
            resolve_names_typ(ctx, symbol_table.clone(), iface_impl.typ.clone());
            if let Some(decl @ Declaration::InterfaceDef(_)) =
                &symbol_table.lookup_declaration(&iface_impl.iface.v)
            {
                ctx.resolution_map.insert(iface_impl.iface.id, decl.clone());
                for (i, prop) in iface_impl.stmts.iter().enumerate() {
                    if let StmtKind::FuncDef(f) = &*prop.kind {
                        if let Some(decl @ Declaration::InterfaceMethod { .. }) =
                            symbol_table.lookup_declaration(&f.name.v)
                        {
                            ctx.resolution_map.insert(f.name.id, decl.clone());
                        }
                        let symbol_table = symbol_table.new_scope();
                        for arg in &f.args {
                            resolve_names_pat(ctx, symbol_table.clone(), arg.0.clone());
                            if let Some(annot) = &arg.1 {
                                resolve_names_typ(ctx, symbol_table.clone(), annot.clone());
                            }
                        }
                        resolve_names_expr(ctx, symbol_table.clone(), f.body.clone());
                        if let Some(ret_type) = &f.ret_type {
                            resolve_names_typ(ctx, symbol_table, ret_type.clone());
                        }
                    }
                }
            } else {
                ctx.unbound_vars.insert(stmt.id);
            }
        }
        ItemKind::Import(..) => {
            // TODO: ensure import was actually resolved by looking up in the symbol table
        }
        ItemKind::TypeDef(tydef) => match &**tydef {
            TypeDefKind::Enum(enum_def) => {
                for ty_arg in &enum_def.ty_args {
                    resolve_names_typ(ctx, symbol_table.clone(), ty_arg.clone());
                }
                for variant in &enum_def.variants {
                    if let Some(associated_data_ty) = &variant.data {
                        resolve_names_typ(ctx, symbol_table.clone(), associated_data_ty.clone());
                    }
                }
            }
            TypeDefKind::Struct(struct_def) => {
                for ty_arg in &struct_def.ty_args {
                    resolve_names_typ(ctx, symbol_table.clone(), ty_arg.clone());
                }
                for field in &struct_def.fields {
                    resolve_names_typ(ctx, symbol_table.clone(), field.ty.clone());
                }
            }
        },
        ItemKind::Stmt(stmt) => {
            resolve_names_stmt(ctx, symbol_table, stmt.clone());
        }
    }
}

fn resolve_names_stmt(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Stmt>) {
    match &*stmt.kind {
        StmtKind::FuncDef(..) => {
            // TODO: get rid of this. No longer in grammar!
        }
        StmtKind::Expr(expr) => {
            resolve_names_expr(ctx, symbol_table, expr.clone());
        }
        StmtKind::Let(_mutable, (pat, ty), expr) => {
            resolve_names_pat(ctx, symbol_table.clone(), pat.clone());
            if let Some(ty_annot) = &ty {
                resolve_names_typ(ctx, symbol_table.clone(), ty_annot.clone());
            }
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
        }
        StmtKind::Set(lhs, rhs) => {
            resolve_names_expr(ctx, symbol_table.clone(), lhs.clone());
            resolve_names_expr(ctx, symbol_table.clone(), rhs.clone());
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
        ExprKind::Identifier(symbol) => {
            let lookup = symbol_table.lookup_declaration(symbol);
            if let Some(decl) = lookup {
                ctx.resolution_map.insert(expr.id, decl);
            } else {
                ctx.unbound_vars.insert(expr.id());
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
        ExprKind::Func(args, out_ty, body) => {
            let symbol_table = symbol_table.new_scope();
            resolve_names_func_helper(ctx, symbol_table.clone(), args, body);
            if let Some(ty_annot) = &out_ty {
                resolve_names_typ(ctx, symbol_table.clone(), ty_annot.clone());
            }
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
            // TODO: if "expr" ends up being a namespace, resolve the field?
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
    args: &[ArgAnnotated],
    body: &Rc<Expr>,
) {
    for arg in args {
        resolve_names_pat(ctx, symbol_table.clone(), arg.0.clone());
        if let Some(ty_annot) = &arg.1 {
            resolve_names_typ(ctx, symbol_table.clone(), ty_annot.clone());
        }
    }

    resolve_names_expr(ctx, symbol_table.clone(), body.clone());
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
            symbol_table.extend_declaration(identifier.clone(), Declaration::Var(pat.id));
        }
        PatKind::Variant(tag, data) => {
            if let Some(decl @ Declaration::EnumVariant { .. }) =
                &symbol_table.lookup_declaration(&tag.v)
            {
                ctx.resolution_map.insert(tag.id, decl.clone());
            } else {
                // TODO: log error
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

fn resolve_names_typ(ctx: &mut StaticsContext, symbol_table: SymbolTable, typ: Rc<Type>) {
    match &*typ.kind {
        TypeKind::Bool | TypeKind::Unit | TypeKind::Int | TypeKind::Float | TypeKind::Str => {}
        // TODO: resolve polymorphic identifier?
        TypeKind::Poly(identifier, ifaces) => {
            for iface in ifaces {
                if let Some(decl @ Declaration::InterfaceDef { .. }) =
                    &symbol_table.lookup_declaration(&iface.v)
                {
                    ctx.resolution_map.insert(iface.id, decl.clone());
                } else {
                    // TODO: log error
                }
            }
        }
        TypeKind::Identifier(identifier) => {
            resolve_names_typ_identifier(ctx, symbol_table, identifier, typ.id);
        }
        TypeKind::Ap(identifier, args) => {
            resolve_names_typ_identifier(ctx, symbol_table.clone(), &identifier.v, identifier.id);
            for arg in args {
                resolve_names_typ(ctx, symbol_table.clone(), arg.clone());
            }
        }
        TypeKind::Function(args, out) => {
            for arg in args {
                resolve_names_typ(ctx, symbol_table.clone(), arg.clone());
            }
            resolve_names_typ(ctx, symbol_table.clone(), out.clone());
        }
        TypeKind::Tuple(elems) => {
            for elem in elems {
                resolve_names_typ(ctx, symbol_table.clone(), elem.clone());
            }
        }
    }
}

fn resolve_names_typ_identifier(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    identifier: &String,
    id: NodeId,
) {
    let lookup = symbol_table.lookup_declaration(identifier);
    match lookup {
        Some(decl @ (Declaration::Struct(_) | Declaration::Enum(_) | Declaration::Array)) => {
            ctx.resolution_map.insert(id, decl);
        }
        _ => {
            // TODO: log error
            // ctx.unbound_vars.insert(id);
        }
    }
}
