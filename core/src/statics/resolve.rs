use std::collections::{BTreeMap, HashMap};
use std::{fmt, rc::Rc};

use crate::ast::{
    ArgAnnotated, Expr, ExprKind, FileAst, Identifier, Node, NodeId, Pat, PatKind, Stmt, StmtKind,
    TypeDefKind, TypeKind,
};
use crate::builtin::Builtin;
use crate::environment::Environment;

use super::{Declaration, Namespace, Resolution, StaticsContext, TypeVar};

// TODO: constrain, Env, Prov should be implementation details
// TODO: others should probably be implementation details too
use super::typecheck::{
    ast_type_to_statics_type, ast_type_to_statics_type_interface, constrain, Prov, SymbolTable,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct EnumDef {
    pub(crate) name: Identifier,
    pub(crate) params: Vec<Identifier>,
    pub(crate) variants: Vec<Variant>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Variant {
    pub(crate) ctor: Identifier,
    pub(crate) data: TypeVar,
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.ctor, self.data)
    }
}

// TODO: these are all kind of redundant... Just use AST nodes instead of putting the same info in these structs?
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructDef {
    pub(crate) name: Identifier,
    pub(crate) params: Vec<Identifier>,
    pub(crate) fields: Vec<StructField>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructField {
    pub(crate) name: Identifier,
    pub(crate) ty: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceDef {
    pub(crate) name: Identifier,
    pub(crate) methods: Vec<InterfaceDefMethod>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceImpl {
    pub(crate) name: Identifier,
    pub(crate) typ: TypeVar,
    pub(crate) methods: Vec<InterfaceImplMethod>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceDefMethod {
    pub(crate) name: Identifier,
    pub(crate) ty: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceImplMethod {
    pub(crate) name: Identifier,
    pub(crate) method_location: NodeId,
    pub(crate) identifier_location: NodeId,
}

pub(crate) fn scan_declarations(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable, // TODO get rid of Env here
    files: Vec<Rc<FileAst>>,
) {
    for file in files {
        let name = file.name.clone();
        let namespace = gather_declarations_file(ctx, symbol_table.clone(), file.clone());
        ctx.global_namespace.children.insert(name, namespace);
    }
}

fn gather_declarations_file(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    file: Rc<FileAst>,
) -> Namespace {
    let mut namespace = Namespace::default();

    // TODO: get rid of this
    for statement in file.statements.iter() {
        gather_definitions_stmt_DEPRECATE(ctx, symbol_table.clone(), statement.clone());
    }

    let qualifiers = vec![file.name.clone()];
    for statement in file.statements.iter() {
        gather_declarations_stmt(&mut namespace, qualifiers.clone(), statement.clone());
    }

    namespace
}

fn gather_declarations_stmt(namespace: &mut Namespace, qualifiers: Vec<String>, stmt: Rc<Stmt>) {
    match &*stmt.kind {
        StmtKind::InterfaceDef(_ident, properties) => {
            // TODO: in the near future, put interface methods in a namespace named after the interface
            // and call interface methods using the dot operator. my_struct.to_string() etc.

            for (i, p) in properties.iter().enumerate() {
                let method_name = p.ident.clone();
                let mut fully_qualified_name = qualifiers.clone();
                fully_qualified_name.push(method_name.clone());
                namespace.declarations.insert(
                    method_name,
                    Declaration::InterfaceMethod {
                        parent: stmt.id,
                        idx: i as u16,
                    },
                );
            }
        }
        StmtKind::InterfaceImpl(_, _, _) => {}
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(_ident, _) => {
                // TODO: type aliases
                // At this stage, since we're just gathering declarations,
                // actually resolving the alias to the final result will have to be done later.
            }
            TypeDefKind::Enum(_ident, _, variants) => {
                // TODO: in the near future, put enum variants in a namespace named after the enum
                // and refer to them in code by just writing .Variant

                for (i, v) in variants.iter().enumerate() {
                    let tag = i as u16;
                    let variant_name = v.ctor.clone();
                    let arity = v.data.as_ref().map_or(0, |d| match &*d.typekind {
                        TypeKind::Tuple(elems) => elems.len(),
                        TypeKind::Unit => 0,
                        _ => 1,
                    }) as u16;

                    namespace.declarations.insert(
                        variant_name,
                        Declaration::Variant {
                            parent: stmt.id,
                            idx: i as u16,
                        },
                    );
                }
            }
            TypeDefKind::Struct(ident, _, fields) => {
                let entry_name = ident.clone();
                namespace
                    .declarations
                    .insert(entry_name, Declaration::Struct(stmt.id));
            }
        },
        StmtKind::Expr(_) => {}
        StmtKind::Let(_, _, _) => {}
        StmtKind::FuncDef(name, _args, _out_annot, _) => {
            let entry_name = name.kind.get_identifier_of_variable();
            let mut fully_qualified_name = qualifiers.clone();
            fully_qualified_name.push(entry_name.clone());
            namespace
                .declarations
                .insert(entry_name, Declaration::FreeFunction(stmt.id));
        }
        StmtKind::Set(..) | StmtKind::Import(..) => {}
    }
}

fn gather_definitions_stmt_DEPRECATE(
    ctx: &mut StaticsContext,
    symbol_table: SymbolTable,
    stmt: Rc<Stmt>,
) {
    match &*stmt.kind {
        StmtKind::InterfaceDef(ident, properties) => {
            if let Some(interface_def) = ctx.interface_defs.get(ident) {
                let entry = ctx
                    .multiple_interface_defs
                    .entry(ident.clone())
                    .or_default();
                entry.push(interface_def.location);
                entry.push(stmt.id);
                return;
            }
            let mut methods = vec![];
            for p in properties {
                let ty_annot = ast_type_to_statics_type_interface(ctx, p.ty.clone(), Some(ident));
                let node_ty = TypeVar::from_node(ctx, p.id());
                // TODO: it would be nice if there were no calls to constrain() when gathering declarations...
                constrain(node_ty.clone(), ty_annot.clone());
                methods.push(InterfaceDefMethod {
                    name: p.ident.clone(),
                    ty: node_ty.clone(),
                });
                ctx.method_to_interface
                    .insert(p.ident.clone(), ident.clone());
                symbol_table.extend(p.ident.clone(), node_ty);
            }
            ctx.interface_defs.insert(
                ident.clone(),
                InterfaceDef {
                    name: ident.clone(),
                    methods,
                    location: stmt.id,
                },
            );
        }
        StmtKind::InterfaceImpl(ident, typ, stmts) => {
            let typ = ast_type_to_statics_type(ctx, typ.clone());

            if typ.is_instantiated_enum() {
                ctx.interface_impl_for_instantiated_ty.push(stmt.id);
            }

            let methods = stmts
                .iter()
                .map(|stmt| match &*stmt.kind {
                    StmtKind::FuncDef(pat, _, _, _) => {
                        let ident = pat.kind.get_identifier_of_variable();
                        InterfaceImplMethod {
                            name: ident,
                            identifier_location: pat.id(),
                            method_location: stmt.id(),
                        }
                    }
                    _ => unreachable!(),
                })
                .collect();
            let impl_list = ctx.interface_impls.entry(ident.clone()).or_default();
            impl_list.push(InterfaceImpl {
                name: ident.clone(),
                typ,
                methods,
                location: stmt.id,
            });
        }
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(_ident, _ty) => {}
            TypeDefKind::Enum(ident, params, variants) => {
                if let Some(enum_def) = ctx.enum_defs.get(ident) {
                    let entry = ctx.multiple_udt_defs.entry(ident.clone()).or_default();
                    entry.push(enum_def.location);
                    entry.push(stmt.id);
                    return;
                }
                let mut defvariants = vec![];
                for (i, v) in variants.iter().enumerate() {
                    let arity = v.data.as_ref().map_or(0, |d| match &*d.typekind {
                        TypeKind::Tuple(elems) => elems.len(),
                        TypeKind::Unit => 0,
                        _ => 1,
                    });
                    symbol_table.extend_declaration(
                        v.ctor.clone(),
                        Resolution::VariantCtor(i as u16, arity as u16),
                    );

                    let data = {
                        if let Some(data) = &v.data {
                            ast_type_to_statics_type(ctx, data.clone())
                        } else {
                            TypeVar::make_unit(Prov::VariantNoData(Box::new(Prov::Node(v.id))))
                        }
                    };
                    defvariants.push(Variant {
                        ctor: v.ctor.clone(),
                        data,
                    });
                    ctx.variants_to_enum.insert(v.ctor.clone(), ident.clone());
                }
                let mut defparams = vec![];
                for p in params {
                    let TypeKind::Poly(ident, _) = &*p.typekind else {
                        panic!("expected poly type for type definition parameter")
                    };
                    defparams.push(ident.clone());
                }
                ctx.enum_defs.insert(
                    ident.clone(),
                    EnumDef {
                        name: ident.clone(),
                        params: defparams,
                        variants: defvariants,
                        location: stmt.id,
                    },
                );
            }
            TypeDefKind::Struct(ident, params, fields) => {
                symbol_table
                    .extend_declaration(ident.clone(), Resolution::StructCtor(fields.len() as u16));

                // let ty_struct = TypeVar::from_node(ctx, stmt.id);
                if let Some(struct_def) = ctx.struct_defs.get(ident) {
                    let entry = ctx.multiple_udt_defs.entry(ident.clone()).or_default();
                    entry.push(struct_def.location);
                    entry.push(stmt.id);
                    return;
                }
                let mut defparams = vec![];
                for p in params {
                    let TypeKind::Poly(ident, _) = &*p.typekind else {
                        panic!("expected poly type for type definition parameter")
                    };
                    defparams.push(ident.clone());
                }
                let mut deffields = vec![];
                for f in fields {
                    let ty_annot = ast_type_to_statics_type(ctx, f.ty.clone());
                    deffields.push(StructField {
                        name: f.ident.clone(),
                        ty: ty_annot.clone(),
                    });

                    let prov = Prov::StructField(f.ident.clone(), stmt.id);
                    let ty_field = TypeVar::fresh(ctx, prov.clone());
                    constrain(ty_field.clone(), ty_annot.clone());
                    ctx.vars.insert(prov, ty_field);
                }
                ctx.struct_defs.insert(
                    ident.clone(),
                    StructDef {
                        name: ident.clone(),
                        params: defparams,
                        fields: deffields,
                        location: stmt.id,
                    },
                );
            }
        },
        StmtKind::Expr(_) => {}
        StmtKind::Let(_, _, _) => {}
        StmtKind::FuncDef(name, _args, _out_annot, _) => {
            let name_id = name.id;
            let name = name.kind.get_identifier_of_variable();
            ctx.fun_defs.insert(name.clone(), stmt.clone());
            symbol_table.extend(name.clone(), TypeVar::from_node(ctx, name_id));
            symbol_table.extend_declaration(name.clone(), Resolution::FreeFunction(stmt.id, name));
        }
        StmtKind::Set(..) => {}
        StmtKind::Import(..) => {}
    }
}

type Env = Environment<Identifier, Declaration>;

// TODO: make a custom type to detect collisions
pub type ToplevelEnv = BTreeMap<Identifier, Declaration>;

pub(crate) fn resolve_imports(
    ctx: &mut StaticsContext,
    files: Vec<Rc<FileAst>>,
) -> BTreeMap<String, ToplevelEnv> {
    let mut envs = BTreeMap::new();
    for file in files {
        envs.insert(file.name.clone(), resolve_imports_file(ctx, file.clone()));
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
        .children
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
        .children
        .get("prelude")
        .unwrap()
        .declarations
        .iter()
    {
        env.insert(name.clone(), declaration.clone());
    }

    for stmt in file.statements.iter() {
        if let StmtKind::Import(path) = &*stmt.kind {
            // add declarations from this import to the environment
            for (name, declaration) in ctx
                .global_namespace
                .children
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

// pub(crate) fn resolve_names_file(ctx: &mut StaticsContext, env: Env, file: Rc<FileAst>) {
//     for (i, eff) in ctx.effects.iter().enumerate() {
//         env.extend(eff.name.clone(), Declaration::Effect(i as u16));
//     }
//     for builtin in Builtin::enumerate().iter() {
//         env.extend(builtin.name(), Declaration::Builtin(*builtin));
//     }
//     for statement in file.statements.iter() {
//         resolve_names_stmt(ctx, env.clone(), statement.clone());
//     }
// }

// fn resolve_names_expr(ctx: &mut StaticsContext, env: Env, expr: Rc<Expr>) {
//     match &*expr.kind {
//         ExprKind::Unit
//         | ExprKind::Int(_)
//         | ExprKind::Float(_)
//         | ExprKind::Bool(_)
//         | ExprKind::Str(_) => {}
//         ExprKind::List(exprs) => {
//             for expr in exprs {
//                 resolve_names_expr(ctx, env.clone(), expr.clone());
//             }
//         }
//         ExprKind::Array(exprs) => {
//             for expr in exprs {
//                 resolve_names_expr(ctx, env.clone(), expr.clone());
//             }
//         }
//         ExprKind::Identifier(symbol) => {
//             let lookup = env.lookup(symbol);
//             if let Some(resolution) = lookup {
//                 ctx.name_resolutions2.insert(expr.id, resolution);
//             } else {
//                 ctx.unbound_vars.insert(expr.id());
//             }
//         }
//         ExprKind::BinOp(left, _, right) => {
//             resolve_names_expr(ctx, env.clone(), left.clone());
//             resolve_names_expr(ctx, env, right.clone());
//         }
//         ExprKind::Block(statements) => {
//             let env = env.new_scope();
//             for statement in statements.iter() {
//                 resolve_names_stmt(ctx, env.clone(), statement.clone());
//             }
//         }
//         ExprKind::If(cond, expr1, expr2) => {
//             resolve_names_expr(ctx, env.clone(), cond.clone());
//             resolve_names_expr(ctx, env.clone(), expr1.clone());
//             if let Some(expr2) = expr2 {
//                 resolve_names_expr(ctx, env.clone(), expr2.clone());
//             }
//         }
//         ExprKind::WhileLoop(cond, expr) => {
//             resolve_names_expr(ctx, env.clone(), cond.clone());
//             resolve_names_expr(ctx, env.clone(), expr.clone());
//         }
//         ExprKind::Match(scrut, arms) => {
//             resolve_names_expr(ctx, env.clone(), scrut.clone());
//             for arm in arms {
//                 let env = env.new_scope();
//                 resolve_names_pat(ctx, env.clone(), arm.pat.clone());
//                 resolve_names_expr(ctx, env.clone(), arm.expr.clone());
//             }
//         }
//         ExprKind::Func(args, _, body) => {
//             let env = env.new_scope();
//             resolve_names_func_helper(ctx, env, args, body);
//         }
//         ExprKind::FuncAp(func, args) => {
//             resolve_names_expr(ctx, env.clone(), func.clone());
//             for arg in args {
//                 resolve_names_expr(ctx, env.clone(), arg.clone());
//             }
//         }
//         ExprKind::Tuple(exprs) => {
//             for expr in exprs {
//                 resolve_names_expr(ctx, env.clone(), expr.clone());
//             }
//         }
//         ExprKind::MemberAccess(expr, field) => {
//             resolve_names_expr(ctx, env.clone(), expr.clone());
//             resolve_names_expr(ctx, env.clone(), field.clone());
//         }
//         ExprKind::IndexAccess(accessed, index) => {
//             resolve_names_expr(ctx, env.clone(), accessed.clone());
//             resolve_names_expr(ctx, env.clone(), index.clone());
//         }
//     }
// }

// fn resolve_names_func_helper(
//     ctx: &mut StaticsContext,
//     env: Env,
//     args: &[ArgAnnotated],
//     body: &Rc<Expr>,
// ) {
//     for arg in args {
//         resolve_names_pat(ctx, env.clone(), arg.0.clone());
//     }

//     resolve_names_expr(ctx, env.clone(), body.clone());
// }

// fn resolve_names_stmt(ctx: &mut StaticsContext, env: Env, stmt: Rc<Stmt>) {
//     match &*stmt.kind {
//         StmtKind::InterfaceDef(..) => {}
//         StmtKind::Import(..) => {}
//         StmtKind::FuncDef(..) => {
//             // TODO: need this probably
//         }
//         StmtKind::InterfaceImpl(..) => { // TODO: need this probably
//         }
//         StmtKind::TypeDef(typdefkind) => match &**typdefkind {
//             TypeDefKind::Alias(ident, ty) => {
//                 let left = TypeVar::fresh(ctx, Prov::Alias(ident.clone()));
//                 let right = ast_type_to_statics_type(ctx, ty.clone());
//                 constrain(left, right);
//             }
//             TypeDefKind::Enum(..) | TypeDefKind::Struct(..) => {}
//         },
//         StmtKind::Expr(expr) => {
//             resolve_names_expr(ctx, env, expr.clone());
//         }
//         StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
//             resolve_names_expr(ctx, env.clone(), expr.clone());
//             resolve_names_pat(ctx, env.clone(), pat.clone());
//         }
//         StmtKind::Set(lhs, rhs) => {
//             resolve_names_expr(ctx, env.clone(), lhs.clone());
//             resolve_names_expr(ctx, env.clone(), rhs.clone());
//         }
//     }
// }

// fn resolve_names_pat(_ctx: &mut StaticsContext, env: Env, pat: Rc<Pat>) {
//     match &*pat.kind {
//         PatKind::Wildcard => (),
//         PatKind::Unit
//         | PatKind::Int(_)
//         | PatKind::Float(_)
//         | PatKind::Bool(_)
//         | PatKind::Str(_) => {}
//         PatKind::Var(identifier) => {
//             env.extend(identifier.clone(), Declaration::Var(pat.id));
//         }
//         PatKind::Variant(_, data) => {
//             if let Some(data) = data {
//                 resolve_names_pat(_ctx, env, data.clone())
//             };
//         }
//         PatKind::Tuple(pats) => {
//             for pat in pats {
//                 resolve_names_pat(_ctx, env.clone(), pat.clone());
//             }
//         }
//     }
// }
