use std::cell::RefCell;
use std::collections::BTreeMap;
use std::{fmt, rc::Rc};

use crate::ast::{
    ArgAnnotated, Expr, ExprKind, FileAst, Identifier, Item, ItemKind, Node, NodeId, Pat, PatKind,
    Stmt, StmtKind, TypeDefKind, TypeKind,
};

use super::{Declaration, Namespace, Resolution_OLD, StaticsContext, TypeVar};

// TODO: constrain, symbol_table,Prov should be implementation details
// TODO: others should probably be implementation details too
use super::typecheck::{
    ast_type_to_statics_type, ast_type_to_statics_type_interface, constrain, Prov, SymbolTable_OLD,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct EnumDef_OLD {
    pub(crate) name: Identifier,
    pub(crate) params: Vec<Identifier>,
    pub(crate) variants: Vec<Variant_OLD>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Variant_OLD {
    pub(crate) ctor: Identifier,
    pub(crate) data: TypeVar,
}

impl fmt::Display for Variant_OLD {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.ctor, self.data)
    }
}

// TODO: these are all kind of redundant... Just use AST nodes instead of putting the same info in these structs?
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructDef_OLD {
    pub(crate) name: Identifier,
    pub(crate) params: Vec<Identifier>,
    pub(crate) fields: Vec<StructField_OLD>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructField_OLD {
    pub(crate) name: Identifier,
    pub(crate) ty: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceDef_OLD {
    pub(crate) name: Identifier,
    pub(crate) methods: Vec<InterfaceDefMethod_OLD>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceImpl_OLD {
    pub(crate) name: Identifier,
    pub(crate) typ: TypeVar,
    pub(crate) methods: Vec<InterfaceImplMethod_OLD>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceDefMethod_OLD {
    pub(crate) name: Identifier,
    pub(crate) ty: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceImplMethod_OLD {
    pub(crate) name: Identifier,
    pub(crate) method_location: NodeId,
    pub(crate) identifier_location: NodeId,
}

pub(crate) fn scan_declarations(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable_OLD, // TODO get rid of Env here
    files: Vec<Rc<FileAst>>,
) {
    for file in files {
        let name = file.name.clone();
        let namespace = gather_declarations_file(ctx, symbol_table.clone(), file.clone());
        ctx.global_namespace
            .namespaces
            .insert(name, namespace.into());
    }
}

fn gather_declarations_file(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable_OLD,
    file: Rc<FileAst>,
) -> Namespace {
    let mut namespace = Namespace::default();

    // TODO: get rid of this
    for item in file.items.iter() {
        gather_definitions_item_DEPRECATE(ctx, symbol_table.clone(), item.clone());
    }

    let qualifiers = vec![file.name.clone()];
    for item in file.items.iter() {
        gather_declarations_item(&mut namespace, qualifiers.clone(), item.clone());
    }

    namespace
}

fn gather_declarations_item(namespace: &mut Namespace, qualifiers: Vec<String>, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::Stmt(..) => {}
        ItemKind::InterfaceDef(iface) => {
            // TODO: in the near future, put interface methods in a namespace named after the interface
            // and call interface methods using the dot operator. my_struct.to_string() etc.

            for (i, p) in iface.props.iter().enumerate() {
                let method_name = p.ident.clone();
                let mut fully_qualified_name = qualifiers.clone();
                fully_qualified_name.push(method_name.clone());
                namespace.declarations.insert(
                    method_name,
                    Declaration::InterfaceMethod {
                        parent: iface.clone(),
                        idx: i as u16,
                    },
                );
            }
        }
        ItemKind::InterfaceImpl(_, _, _) => {}
        ItemKind::TypeDef(typdefkind) => match &**typdefkind {
            // TypeDefKind::Alias(_ident, _) => {
            //     // At this stage, since we're just gathering declarations,
            //     // actually resolving the alias to the final result will have to be done later.
            // }
            TypeDefKind::Enum(e) => {
                // TODO: in the near future, put enum variants in a namespace named after the enum
                // and refer to them in code by just writing .Variant

                for (i, v) in e.variants.iter().enumerate() {
                    let tag = i as u16;
                    let variant_name = v.ctor.clone();
                    let arity = v.data.as_ref().map_or(0, |d| match &*d.typekind {
                        TypeKind::Tuple(elems) => elems.len(),
                        TypeKind::Unit => 0,
                        _ => 1,
                    }) as u16;

                    namespace.declarations.insert(
                        variant_name,
                        Declaration::EnumVariant {
                            parent: e.clone(),
                            idx: i as u16,
                        },
                    );
                }
            }
            TypeDefKind::Struct(s) => {
                let entry_name = s.name.clone();
                namespace
                    .declarations
                    .insert(entry_name, Declaration::Struct(s.clone()));
            }
        },
        ItemKind::FuncDef(f) => {
            let entry_name = f.name.kind.get_identifier_of_variable();
            let mut fully_qualified_name = qualifiers.clone();
            fully_qualified_name.push(entry_name.clone());
            namespace
                .declarations
                .insert(entry_name, Declaration::FreeFunction(f.clone()));
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
    declarations: BTreeMap<Identifier, Declaration>,
    namespaces: BTreeMap<Identifier, Rc<Namespace>>,

    enclosing: Option<Rc<RefCell<SymbolTableBase>>>,
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

    pub(crate) fn lookup_declaration(&self, id: &Identifier) -> Option<Declaration> {
        self.base.borrow().declarations.get(id).cloned()
    }

    pub(crate) fn lookup_namespace(&self, id: &Identifier) -> Option<Rc<Namespace>> {
        self.base.borrow().namespaces.get(id).cloned()
    }

    pub(crate) fn extend_declaration(&self, id: Identifier, decl: Declaration) {
        self.base.borrow_mut().declarations.insert(id, decl);
    }

    pub(crate) fn extend_namespace(&self, id: Identifier, ns: Rc<Namespace>) {
        self.base.borrow_mut().namespaces.insert(id, ns);
    }
}

// type Env = Environment<Identifier, Declaration>;

// TODO: make a custom type to detect collisions
pub type ToplevelEnv = BTreeMap<Identifier, Declaration>;

pub(crate) fn resolve(
    ctx: &mut StaticsContext,
    files: Vec<Rc<FileAst>>,
) -> BTreeMap<String, ToplevelEnv> {
    let mut envs = BTreeMap::new();
    for file in files {
        let env = resolve_imports_file(ctx, file.clone());
        resolve_names_file(ctx, env.clone(), file.clone());
        envs.insert(file.name.clone(), env);
    }
    envs
}

fn resolve_imports_file(ctx: &mut StaticsContext, file: Rc<FileAst>) -> ToplevelEnv {
    // Return an environment with all identifiers available to this file.
    // That includes identifiers from this file and all imports.
    let mut env = ToplevelEnv::new();
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

    for item in file.items.iter() {
        if let ItemKind::Import(path) = &*item.kind {
            // add declarations from this import to the environment
            for (name, declaration) in ctx
                .global_namespace
                .namespaces
                .get(path)
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

pub(crate) fn resolve_names_file(ctx: &mut StaticsContext, env: ToplevelEnv, file: Rc<FileAst>) {
    // TODO: probably need these

    let symbol_table = SymbolTable::empty();

    // for (i, eff) in ctx.effects.iter().enumerate() {
    //     env.extend(eff.name.clone(), Declaration::Effect(i as u16));
    // }
    // for builtin in Builtin::enumerate().iter() {
    //     env.extend(builtin.name(), Declaration::Builtin(*builtin));
    // }
    for item in file.items.iter() {
        resolve_names_item(ctx, symbol_table.clone(), item.clone());
    }
}

fn resolve_names_item(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Item>) {
    match &*stmt.kind {
        ItemKind::FuncDef(f) => {
            // TODO: need this probably
        }
        ItemKind::InterfaceDef(..) => {}
        ItemKind::InterfaceImpl(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::TypeDef(..) => {}
        ItemKind::Stmt(stmt) => {
            resolve_names_stmt(ctx, symbol_table, stmt.clone());
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
            // TODO: This is where we update the resolution map
            // let lookup = symbol_table.lookup(symbol);
            // if let Some(decl) = lookup {
            //     ctx.resolution_map.insert(expr.id, decl);
            // } else {
            //     ctx.unbound_vars.insert(expr.id());
            // }
        }
        ExprKind::BinOp(left, _, right) => {
            resolve_names_expr(ctx, symbol_table.clone(), left.clone());
            resolve_names_expr(ctx, symbol_table, right.clone());
        }
        ExprKind::Block(statements) => {
            let env = symbol_table.new_scope();
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
                let env = symbol_table.new_scope();
                resolve_names_pat(ctx, symbol_table.clone(), arm.pat.clone());
                resolve_names_expr(ctx, symbol_table.clone(), arm.expr.clone());
            }
        }
        ExprKind::Func(args, _, body) => {
            let env = symbol_table.new_scope();
            resolve_names_func_helper(ctx, symbol_table, args, body);
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
            resolve_names_expr(ctx, symbol_table.clone(), field.clone());
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
    }

    resolve_names_expr(ctx, symbol_table.clone(), body.clone());
}

fn resolve_names_stmt(ctx: &mut StaticsContext, symbol_table: SymbolTable, stmt: Rc<Stmt>) {
    match &*stmt.kind {
        StmtKind::FuncDef(..) => {
            // TODO: need this probably
        }
        StmtKind::Expr(expr) => {
            resolve_names_expr(ctx, symbol_table, expr.clone());
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            resolve_names_expr(ctx, symbol_table.clone(), expr.clone());
            resolve_names_pat(ctx, symbol_table.clone(), pat.clone());
        }
        StmtKind::Set(lhs, rhs) => {
            resolve_names_expr(ctx, symbol_table.clone(), lhs.clone());
            resolve_names_expr(ctx, symbol_table.clone(), rhs.clone());
        }
    }
}

fn resolve_names_pat(_ctx: &mut StaticsContext, symbol_table: SymbolTable, pat: Rc<Pat>) {
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Unit
        | PatKind::Int(_)
        | PatKind::Float(_)
        | PatKind::Bool(_)
        | PatKind::Str(_) => {}
        PatKind::Binding(identifier) => {
            // TODO: gonna need this
            // env.extend(identifier.clone(), Declaration::PatBinding(pat.id));
        }
        PatKind::Variant(_, data) => {
            if let Some(data) = data {
                resolve_names_pat(_ctx, symbol_table, data.clone())
            };
        }
        PatKind::Tuple(pats) => {
            for pat in pats {
                resolve_names_pat(_ctx, symbol_table.clone(), pat.clone());
            }
        }
    }
}

///////// DEPRECATE BELOW

fn gather_definitions_item_DEPRECATE(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable_OLD,
    stmt: Rc<Item>,
) {
    match &*stmt.kind {
        ItemKind::InterfaceDef(i) => {
            if let Some(interface_def) = ctx.interface_defs.get(&i.name) {
                let entry = ctx
                    .multiple_interface_defs
                    .entry(i.name.clone())
                    .or_default();
                entry.push(interface_def.location);
                entry.push(stmt.id);
                return;
            }
            let mut methods = vec![];
            for p in i.props.iter() {
                let ty_annot = ast_type_to_statics_type_interface(ctx, p.ty.clone(), Some(&i.name));
                let node_ty = TypeVar::from_node(ctx, p.id());
                // TODO: it would be nice if there were no calls to constrain() when gathering declarations...
                constrain(node_ty.clone(), ty_annot.clone());
                methods.push(InterfaceDefMethod_OLD {
                    name: p.ident.clone(),
                    ty: node_ty.clone(),
                });
                ctx.method_to_interface
                    .insert(p.ident.clone(), i.name.clone());
                symbol_table.extend(p.ident.clone(), node_ty);
            }
            ctx.interface_defs.insert(
                i.name.clone(),
                InterfaceDef_OLD {
                    name: i.name.clone(),
                    methods,
                    location: stmt.id,
                },
            );
        }
        ItemKind::InterfaceImpl(ident, typ, stmts) => {
            let typ = ast_type_to_statics_type(ctx, typ.clone());

            if typ.is_instantiated_enum() {
                ctx.interface_impl_for_instantiated_ty.push(stmt.id);
            }

            let methods = stmts
                .iter()
                .map(|stmt| match &*stmt.kind {
                    StmtKind::FuncDef(f) => {
                        let ident = f.name.kind.get_identifier_of_variable();
                        InterfaceImplMethod_OLD {
                            name: ident,
                            identifier_location: f.name.id(),
                            method_location: stmt.id(),
                        }
                    }
                    _ => unreachable!(),
                })
                .collect();
            let impl_list = ctx.interface_impls.entry(ident.clone()).or_default();
            impl_list.push(InterfaceImpl_OLD {
                name: ident.clone(),
                typ,
                methods,
                location: stmt.id,
            });
        }
        ItemKind::TypeDef(typdefkind) => match &**typdefkind {
            // TypeDefKind::Alias(_ident, _ty) => {}
            TypeDefKind::Enum(e) => {
                if let Some(enum_def) = ctx.enum_defs.get(&e.name) {
                    let entry = ctx.multiple_udt_defs.entry(e.name.clone()).or_default();
                    entry.push(enum_def.location);
                    entry.push(stmt.id);
                    return;
                }
                let mut defvariants = vec![];
                for (i, v) in e.variants.iter().enumerate() {
                    let arity = v.data.as_ref().map_or(0, |d| match &*d.typekind {
                        TypeKind::Tuple(elems) => elems.len(),
                        TypeKind::Unit => 0,
                        _ => 1,
                    });
                    symbol_table.extend_declaration(
                        v.ctor.clone(),
                        Resolution_OLD::VariantCtor(i as u16, arity as u16),
                    );

                    let data = {
                        if let Some(data) = &v.data {
                            ast_type_to_statics_type(ctx, data.clone())
                        } else {
                            TypeVar::make_unit(Prov::VariantNoData(Box::new(Prov::Node(v.id))))
                        }
                    };
                    defvariants.push(Variant_OLD {
                        ctor: v.ctor.clone(),
                        data,
                    });
                    ctx.variants_to_enum.insert(v.ctor.clone(), e.name.clone());
                }
                let mut defparams = vec![];
                for p in e.ty_args.iter() {
                    let TypeKind::Poly(ident, _) = &*p.typekind else {
                        panic!("expected poly type for type definition parameter")
                    };
                    defparams.push(ident.clone());
                }
                ctx.enum_defs.insert(
                    e.name.clone(),
                    EnumDef_OLD {
                        name: e.name.clone(),
                        params: defparams,
                        variants: defvariants,
                        location: stmt.id,
                    },
                );
            }
            TypeDefKind::Struct(s) => {
                symbol_table.extend_declaration(
                    s.name.clone(),
                    Resolution_OLD::StructCtor(s.fields.len() as u16),
                );

                // let ty_struct = TypeVar::from_node(ctx, stmt.id);
                if let Some(struct_def) = ctx.struct_defs.get(&s.name) {
                    let entry = ctx.multiple_udt_defs.entry(s.name.clone()).or_default();
                    entry.push(struct_def.location);
                    entry.push(stmt.id);
                    return;
                }
                let mut defparams = vec![];
                for p in s.ty_args.iter() {
                    let TypeKind::Poly(ident, _) = &*p.typekind else {
                        panic!("expected poly type for type definition parameter")
                    };
                    defparams.push(ident.clone());
                }
                let mut deffields = vec![];
                for f in s.fields.iter() {
                    let ty_annot = ast_type_to_statics_type(ctx, f.ty.clone());
                    deffields.push(StructField_OLD {
                        name: f.ident.clone(),
                        ty: ty_annot.clone(),
                    });

                    let prov = Prov::StructField(f.ident.clone(), stmt.id);
                    let ty_field = TypeVar::fresh(ctx, prov.clone());
                    constrain(ty_field.clone(), ty_annot.clone());
                    ctx.vars.insert(prov, ty_field);
                }
                ctx.struct_defs.insert(
                    s.name.clone(),
                    StructDef_OLD {
                        name: s.name.clone(),
                        params: defparams,
                        fields: deffields,
                        location: stmt.id,
                    },
                );
            }
        },
        ItemKind::FuncDef(f) => {
            let name_id = f.name.id;
            let name = f.name.kind.get_identifier_of_variable();
            ctx.fun_defs.insert(name.clone(), f.clone());
            symbol_table.extend(name.clone(), TypeVar::from_node(ctx, name_id));
            symbol_table
                .extend_declaration(name.clone(), Resolution_OLD::FreeFunction(stmt.id, name));
        }
        ItemKind::Import(..) => {}
        ItemKind::Stmt(..) => {}
    }
}

fn gather_definitions_stmt_DEPRECATE(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable_OLD,
    stmt: Rc<Stmt>,
) {
    match &*stmt.kind {
        StmtKind::Expr(_) => {}
        StmtKind::Let(_, _, _) => {}
        StmtKind::FuncDef(f) => {
            let name_id = f.name.id;
            let name = f.name.kind.get_identifier_of_variable();
            ctx.fun_defs.insert(name.clone(), f.clone());
            symbol_table.extend(name.clone(), TypeVar::from_node(ctx, name_id));
            symbol_table
                .extend_declaration(name.clone(), Resolution_OLD::FreeFunction(stmt.id, name));
        }
        StmtKind::Set(..) => {}
    }
}
