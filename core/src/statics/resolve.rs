use std::{fmt, rc::Rc};

use crate::ast::{Identifier, Node, NodeId, Stmt, StmtKind, FileAst, TypeDefKind, TypeKind};
use crate::builtin::Builtin;
use crate::environment::Environment;

use super::{Declaration, Namespace, Resolution, StaticsContext, TypeVar};

// TODO: constrain, Gamma, Prov should be implementation details
// TODO: others should probably be implementation details too
use super::typecheck::{
    ast_type_to_statics_type, ast_type_to_statics_type_interface, constrain, Gamma, Prov,
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
    gamma: Gamma, // TODO get rid of Gamma here
    files: Vec<Rc<FileAst>>,
) {
    for file in files {
        let name = file.name.clone();
        let namespace = gather_declarations_file(ctx, gamma.clone(), file.clone());
        ctx.global_namespace.children.insert(name, namespace);
    }
}

fn gather_declarations_file(
    ctx: &mut StaticsContext,
    gamma: Gamma,
    file: Rc<FileAst>,
) -> Namespace {
    let mut namespace = Namespace::default();

    // TODO: get rid of this
    for statement in file.statements.iter() {
        gather_definitions_stmt_DEPRECATE(ctx, gamma.clone(), statement.clone());
    }

    let qualifiers = vec![file.name.clone()];
    for statement in file.statements.iter() {
        gather_declarations_stmt(&mut namespace, &qualifiers, statement.clone());
    }

    namespace
}

fn gather_declarations_stmt(namespace: &mut Namespace, qualifiers: &Vec<String>, stmt: Rc<Stmt>) {
    match &*stmt.kind {
        StmtKind::InterfaceDef(ident, properties) => {
            let mut ns = Namespace::default();

            // TODO: handle properties
            for p in properties {
                let method_name = p.ident.clone();
                let mut fully_qualified_name = qualifiers.clone();
                fully_qualified_name.push(method_name.clone());
                ns.declarations.insert(
                    method_name,
                    Declaration::InterfaceMethod(fully_qualified_name),
                );
            }

            namespace.children.insert(ident.clone(), ns);

            // namespace.declarations.insert(entry_name, stmt.id);
        }
        StmtKind::InterfaceImpl(..) => {}
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(ident, _) => {
                // TODO: type aliases
                // At this stage, since we're just gathering declarations,
                // actually resolving the alias to the final result will have to be done later.

                // let entry_name = ident.clone();
                // namespace.declarations.insert(entry_name, stmt.id);
            }
            TypeDefKind::Enum(ident, _, variants) => {
                let mut ns = Namespace::default();
                let name = ident.clone();

                for (i, v) in variants.iter().enumerate() {
                    let tag = i as u16;
                    let variant_name = v.ctor.clone();
                    let arity = v.data.as_ref().map_or(0, |d| match &*d.typekind {
                        TypeKind::Tuple(elems) => elems.len(),
                        TypeKind::Unit => 0,
                        _ => 1,
                    }) as u16;

                    ns.declarations
                        .insert(variant_name, Declaration::VariantCtor(tag, arity));
                }

                namespace.children.insert(name, ns);
            }
            TypeDefKind::Struct(ident, _, fields) => {
                let entry_name = ident.clone();
                namespace
                    .declarations
                    .insert(entry_name, Declaration::StructCtor(fields.len() as u16));
            }
        },
        StmtKind::Expr(_) => {}
        StmtKind::Let(_, _, _) => {}
        StmtKind::FuncDef(name, _args, _out_annot, _) => {
            let entry_name = name.kind.get_identifier_of_variable();
            let mut fully_qualified_name = qualifiers.clone();
            fully_qualified_name.push(entry_name.clone());
            namespace.declarations.insert(
                entry_name,
                Declaration::FreeFunction(stmt.id, fully_qualified_name),
            );
        }
        StmtKind::Set(..) | StmtKind::Import(..) => {}
    }
}

fn gather_definitions_stmt_DEPRECATE(ctx: &mut StaticsContext, gamma: Gamma, stmt: Rc<Stmt>) {
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
                gamma.extend(p.ident.clone(), node_ty);
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
                    gamma.extend_declaration(
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
                gamma
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
            gamma.extend(name.clone(), TypeVar::from_node(ctx, name_id));
            gamma.extend_declaration(name.clone(), Resolution::FreeFunction(stmt.id, name));
        }
        StmtKind::Set(..) => {}
        StmtKind::Import(..) => {}
    }
}

type Env = Environment<Identifier, Declaration>;

pub(crate) fn resolve_all_imports(ctx: &mut StaticsContext, files: Vec<Rc<FileAst>>) {}

fn resolve_imports(ctx: &mut StaticsContext, file: Rc<FileAst>) -> Env {
    // Return an environment with all identifiers available to this file.
    // That includes identifiers from this file and all imports.
    let env = Env::empty();
    // add declarations from this file to the environment
    for (name, declaration) in ctx
        .global_namespace
        .children
        .get(&file.name)
        .unwrap()
        .declarations
        .iter()
    {
        env.extend(name.clone(), declaration.clone());
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
                env.extend(name.clone(), declaration.clone());
            }
        }
    }
    dbg!(&env);
    env
}

// // don't do typechecking
// // just do name resolution for variables and functions etc.
// fn resolve_names_stmt(ctx: &mut StaticsContext, env: Env, stmt: Rc<Stmt>) {
//     match &*stmt.kind {
//         StmtKind::FuncDef(name, _args, _out_annot, _) => {
//             let name = name.kind.get_identifier_of_variable();
//             let resolution = env.lookup(&name);
//             // match resolution {
//             //     EnvEntry::Resolution(res) => {}
//             //     EnvEntry::Namespace(_) => {}
//             // }
//         }
//         _ => {}
//     }
// }

// pub(crate) fn resolve_names_file(ctx: &mut StaticsContext, env: Env, file: Rc<FileAst>) {
//     for (i, eff) in ctx.effects.iter().enumerate() {
//         env.extend(eff.name.clone(), Declaration::Effect(i as u16));
//     }
//     for builtin in Builtin::enumerate().iter() {
//         env.extend(builtin.name(), Declaration::Builtin(*builtin));
//     }
//     for statement in file.statements.iter() {
//         generate_constraints_stmt(env.clone(), Mode::Syn, statement.clone(), ctx, true);
//     }
// }

// fn resolve_names_expr(gamma: Gamma, mode: Mode, expr: Rc<Expr>, ctx: &mut StaticsContext) {
//     let node_ty = TypeVar::from_node(ctx, expr.id);
//     match mode {
//         Mode::Syn => (),
//         Mode::Ana { expected } => constrain(node_ty.clone(), expected),
//     };
//     match &*expr.kind {
//         ExprKind::Unit => {
//             constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)));
//         }
//         ExprKind::Int(_) => {
//             constrain(node_ty, TypeVar::make_int(Prov::Node(expr.id)));
//         }
//         ExprKind::Float(_) => {
//             constrain(node_ty, TypeVar::make_float(Prov::Node(expr.id)));
//         }
//         ExprKind::Bool(_) => {
//             constrain(node_ty, TypeVar::make_bool(Prov::Node(expr.id)));
//         }
//         ExprKind::Str(s) => {
//             constrain(node_ty, TypeVar::make_string(Prov::Node(expr.id)));
//             let len = ctx.string_constants.len();
//             ctx.string_constants.entry(s.clone()).or_insert(len);
//         }
//         ExprKind::List(exprs) => {
//             let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(expr.id).into()));
//             constrain(
//                 node_ty,
//                 TypeVar::make_def_instance(
//                     Prov::Node(expr.id),
//                     "list".to_owned(),
//                     vec![elem_ty.clone()],
//                 ),
//             );
//             for expr in exprs {
//                 generate_constraints_expr(
//                     gamma.clone(),
//                     Mode::Ana {
//                         expected: elem_ty.clone(),
//                     },
//                     expr.clone(),
//                     ctx,
//                 );
//             }
//         }
//         ExprKind::Array(exprs) => {
//             let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(expr.id).into()));
//             constrain(
//                 node_ty,
//                 TypeVar::make_def_instance(
//                     Prov::Node(expr.id),
//                     "array".to_owned(),
//                     vec![elem_ty.clone()],
//                 ),
//             );
//             for expr in exprs {
//                 generate_constraints_expr(
//                     gamma.clone(),
//                     Mode::Ana {
//                         expected: elem_ty.clone(),
//                     },
//                     expr.clone(),
//                     ctx,
//                 );
//             }
//         }
//         ExprKind::Identifier(symbol) => {
//             let lookup = gamma.lookup_declaration(symbol);
//             if let Some(resolution) = lookup {
//                 ctx.name_resolutions.insert(expr.id, resolution);
//             }
//             let lookup = gamma.lookup(symbol);
//             if let Some(typ) = lookup {
//                 // replace polymorphic types with unifvars if necessary
//                 let typ = typ.instantiate(gamma, ctx, Prov::Node(expr.id));
//                 constrain(typ, node_ty);
//                 return;
//             }
//             // TODO: this is incredibly hacky. No respect for scope at all... Should be added at the file with Effects at the least...
//             let enum_def = ctx.enum_def_of_variant(symbol);
//             if let Some(enum_def) = enum_def {
//                 let nparams = enum_def.params.len();
//                 let mut params = vec![];
//                 let mut substitution = BTreeMap::new();
//                 for i in 0..nparams {
//                     params.push(TypeVar::fresh(
//                         ctx,
//                         Prov::InstantiateUdtParam(Box::new(Prov::Node(expr.id)), i as u8),
//                     ));
//                     substitution.insert(enum_def.params[i].clone(), params[i].clone());
//                 }
//                 let def_type = TypeVar::make_def_instance(
//                     Prov::UdtDef(Box::new(Prov::Node(expr.id))),
//                     enum_def.name,
//                     params,
//                 );

//                 let the_variant = enum_def
//                     .variants
//                     .iter()
//                     .find(|v| v.ctor == *symbol)
//                     .unwrap();
//                 if let Some(PotentialType::Unit(_)) = the_variant.data.single() {
//                     constrain(node_ty, def_type);
//                 } else if let Some(PotentialType::Tuple(_, elems)) = &the_variant.data.single() {
//                     let args = elems
//                         .iter()
//                         .map(|e| {
//                             e.clone()
//                                 .subst(gamma.clone(), Prov::Node(expr.id), &substitution)
//                         })
//                         .collect();
//                     constrain(
//                         node_ty,
//                         TypeVar::make_func(args, def_type, Prov::Node(expr.id)),
//                     );
//                 } else {
//                     constrain(
//                         node_ty,
//                         TypeVar::make_func(
//                             vec![the_variant.data.clone().subst(
//                                 gamma,
//                                 Prov::Node(expr.id),
//                                 &substitution,
//                             )],
//                             def_type,
//                             Prov::Node(expr.id),
//                         ),
//                     );
//                 }
//                 return;
//             }
//             let struct_def = ctx.struct_defs.get(symbol).cloned();
//             if let Some(struct_def) = struct_def {
//                 let nparams = struct_def.params.len();
//                 let mut params = vec![];
//                 let mut substitution = BTreeMap::new();
//                 for i in 0..nparams {
//                     params.push(TypeVar::fresh(
//                         ctx,
//                         Prov::InstantiateUdtParam(Box::new(Prov::Node(expr.id)), i as u8),
//                     ));
//                     substitution.insert(struct_def.params[i].clone(), params[i].clone());
//                 }
//                 let def_type = TypeVar::make_def_instance(
//                     Prov::UdtDef(Box::new(Prov::Node(expr.id))),
//                     struct_def.name.clone(),
//                     params,
//                 );
//                 let fields = struct_def
//                     .fields
//                     .iter()
//                     .map(|f| {
//                         f.ty.clone()
//                             .subst(gamma.clone(), Prov::Node(expr.id), &substitution)
//                     })
//                     .collect();
//                 constrain(
//                     node_ty,
//                     TypeVar::make_func(fields, def_type, Prov::Node(expr.id)),
//                 );
//                 return;
//             }
//             ctx.unbound_vars.insert(expr.id());
//         }
//         ExprKind::BinOp(left, op, right) => {
//             let (ty_left, ty_right, ty_out) = types_of_binop(op, expr.id);
//             let (ty_left, ty_right, ty_out) = (
//                 ty_left.instantiate(gamma.clone(), ctx, Prov::Node(expr.id)),
//                 ty_right.instantiate(gamma.clone(), ctx, Prov::Node(expr.id)),
//                 ty_out.instantiate(gamma.clone(), ctx, Prov::Node(expr.id)),
//             );
//             constrain(ty_out, node_ty);
//             generate_constraints_expr(
//                 gamma.clone(),
//                 Mode::Ana { expected: ty_left },
//                 left.clone(),
//                 ctx,
//             );
//             generate_constraints_expr(gamma, Mode::Ana { expected: ty_right }, right.clone(), ctx);
//         }
//         ExprKind::Block(statements) => {
//             if statements.is_empty() {
//                 constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)));
//                 return;
//             }
//             let new_gamma = gamma.new_scope();
//             for statement in statements[..statements.len() - 1].iter() {
//                 generate_constraints_stmt(
//                     new_gamma.clone(),
//                     Mode::Syn,
//                     statement.clone(),
//                     ctx,
//                     true,
//                 );
//             }
//             // if last statement is an expression, the block will have that expression's type
//             if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().kind {
//                 generate_constraints_expr(
//                     new_gamma,
//                     Mode::Ana { expected: node_ty },
//                     terminal_expr.clone(),
//                     ctx,
//                 )
//             } else {
//                 generate_constraints_stmt(
//                     new_gamma,
//                     Mode::Syn,
//                     statements.last().unwrap().clone(),
//                     ctx,
//                     true,
//                 );
//                 constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
//             }
//         }
//         ExprKind::If(cond, expr1, expr2) => {
//             generate_constraints_expr(
//                 gamma.clone(),
//                 Mode::Ana {
//                     expected: TypeVar::make_bool(Prov::Node(cond.id)),
//                 },
//                 cond.clone(),
//                 ctx,
//             );
//             match &expr2 {
//                 // if-else
//                 Some(expr2) => {
//                     generate_constraints_expr(
//                         gamma.clone(),
//                         Mode::Ana {
//                             expected: node_ty.clone(),
//                         },
//                         expr1.clone(),
//                         ctx,
//                     );
//                     generate_constraints_expr(
//                         gamma,
//                         Mode::Ana { expected: node_ty },
//                         expr2.clone(),
//                         ctx,
//                     );
//                 }
//                 // just if
//                 None => {
//                     generate_constraints_expr(
//                         gamma,
//                         Mode::Ana {
//                             expected: TypeVar::make_unit(Prov::Node(expr.id)),
//                         },
//                         expr1.clone(),
//                         ctx,
//                     );
//                     constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
//                 }
//             }
//         }
//         ExprKind::WhileLoop(cond, expr) => {
//             generate_constraints_expr(
//                 gamma.clone(),
//                 Mode::Ana {
//                     expected: TypeVar::make_bool(Prov::Node(cond.id)),
//                 },
//                 cond.clone(),
//                 ctx,
//             );
//             generate_constraints_expr(gamma, Mode::Syn, expr.clone(), ctx);
//             constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
//         }
//         ExprKind::Match(scrut, arms) => {
//             let ty_scrutiny = TypeVar::from_node(ctx, scrut.id);
//             generate_constraints_expr(
//                 gamma.clone(),
//                 Mode::Ana {
//                     expected: ty_scrutiny.clone(),
//                 },
//                 scrut.clone(),
//                 ctx,
//             );
//             for arm in arms {
//                 let new_gamma = gamma.new_scope();
//                 generate_constraints_pat(
//                     new_gamma.clone(),
//                     Mode::Ana {
//                         expected: ty_scrutiny.clone(),
//                     },
//                     arm.pat.clone(),
//                     ctx,
//                 );
//                 generate_constraints_expr(
//                     new_gamma,
//                     Mode::Ana {
//                         expected: node_ty.clone(),
//                     },
//                     arm.expr.clone(),
//                     ctx,
//                 );
//             }
//         }
//         ExprKind::Func(args, out_annot, body) => {
//             let func_node_id = expr.id;
//             let body_gamma = gamma.new_scope();
//             let ty_func = generate_constraints_func_helper(
//                 ctx,
//                 func_node_id,
//                 body_gamma,
//                 args,
//                 out_annot,
//                 body,
//             );

//             constrain(node_ty, ty_func);
//         }
//         ExprKind::FuncAp(func, args) => {
//             // arguments
//             let tys_args: Vec<TypeVar> = args
//                 .iter()
//                 .enumerate()
//                 .map(|(n, arg)| {
//                     let unknown =
//                         TypeVar::fresh(ctx, Prov::FuncArg(Box::new(Prov::Node(func.id)), n as u8));
//                     generate_constraints_expr(
//                         gamma.clone(),
//                         Mode::Ana {
//                             expected: unknown.clone(),
//                         },
//                         arg.clone(),
//                         ctx,
//                     );
//                     unknown
//                 })
//                 .collect();

//             // body
//             let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(Box::new(Prov::Node(func.id))));
//             constrain(ty_body.clone(), node_ty);

//             // function type
//             let ty_func = TypeVar::make_func(tys_args, ty_body, Prov::Node(expr.id));
//             generate_constraints_expr(
//                 gamma,
//                 Mode::Ana {
//                     expected: ty_func.clone(),
//                 },
//                 func.clone(),
//                 ctx,
//             );

//             // println!("funcap: {}", ty_func);
//         }
//         ExprKind::Tuple(exprs) => {
//             let tys = exprs
//                 .iter()
//                 .map(|expr| TypeVar::fresh(ctx, Prov::Node(expr.id)))
//                 .collect();
//             constrain(node_ty, TypeVar::make_tuple(tys, Prov::Node(expr.id)));
//             for expr in exprs {
//                 generate_constraints_expr(gamma.clone(), Mode::Syn, expr.clone(), ctx);
//             }
//         }
//         ExprKind::MemberAccess(expr, field) => {
//             generate_constraints_expr(gamma, Mode::Syn, expr.clone(), ctx);
//             let ty_expr = TypeVar::fresh(ctx, Prov::Node(expr.id));
//             if ty_expr.underdetermined() {
//                 ctx.annotation_needed.insert(expr.id);
//                 return;
//             }
//             let Some(inner) = ty_expr.single() else {
//                 return;
//             };
//             if let PotentialType::UdtInstance(_, ident, _) = inner {
//                 if let Some(struct_def) = ctx.struct_defs.get(&ident) {
//                     let ExprKind::Identifier(field_ident) = &*field.kind else {
//                         ctx.field_not_ident.insert(field.id);
//                         return;
//                     };
//                     let ty_field = TypeVar::fresh(
//                         ctx,
//                         Prov::StructField(field_ident.clone(), struct_def.location),
//                     );
//                     constrain(node_ty.clone(), ty_field);
//                     return;
//                 }
//             }

//             ctx.types_that_must_be_structs.insert(ty_expr, expr.id);
//         }
//         ExprKind::IndexAccess(accessed, index) => {
//             generate_constraints_expr(gamma.clone(), Mode::Syn, accessed.clone(), ctx);

//             let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(accessed.id).into()));
//             let accessed_ty = TypeVar::from_node(ctx, accessed.id);
//             constrain(
//                 accessed_ty,
//                 TypeVar::make_def_instance(
//                     Prov::Node(accessed.id),
//                     "array".to_owned(),
//                     vec![elem_ty.clone()],
//                 ),
//             );
//             generate_constraints_expr(
//                 gamma,
//                 Mode::Ana {
//                     expected: TypeVar::make_int(Prov::IndexAccess),
//                 },
//                 index.clone(),
//                 ctx,
//             );

//             constrain(node_ty, elem_ty);
//         }
//     }
// }

// fn resolve_names_func_helper(
//     ctx: &mut StaticsContext,
//     node_id: NodeId,
//     gamma: Gamma,
//     args: &[ArgAnnotated],
//     out_annot: &Option<Rc<AstType>>,
//     body: &Rc<Expr>,
// ) -> TypeVar {
//     // arguments
//     let ty_args = args
//         .iter()
//         .map(|(arg, arg_annot)| {
//             let ty_pat = TypeVar::from_node(ctx, arg.id);
//             match arg_annot {
//                 Some(arg_annot) => {
//                     let ty_annot = TypeVar::from_node(ctx, arg_annot.id());
//                     let arg_annot = ast_type_to_statics_type(ctx, arg_annot.clone());
//                     constrain(ty_annot.clone(), arg_annot.clone());
//                     gamma.add_polys(&arg_annot);
//                     generate_constraints_pat(
//                         gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
//                         Mode::Ana { expected: ty_annot },
//                         arg.clone(),
//                         ctx,
//                     )
//                 }
//                 None => generate_constraints_pat(gamma.clone(), Mode::Syn, arg.clone(), ctx),
//             }
//             ty_pat
//         })
//         .collect();

//     // body
//     let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(Box::new(Prov::Node(node_id))));
//     generate_constraints_expr(
//         gamma.clone(),
//         Mode::Ana {
//             expected: ty_body.clone(),
//         },
//         body.clone(),
//         ctx,
//     );
//     if let Some(out_annot) = out_annot {
//         let out_annot = ast_type_to_statics_type(ctx, out_annot.clone());
//         gamma.add_polys(&out_annot);
//         generate_constraints_expr(
//             gamma,
//             Mode::Ana {
//                 expected: out_annot,
//             },
//             body.clone(),
//             ctx,
//         );
//     }

//     TypeVar::make_func(ty_args, ty_body, Prov::Node(node_id))
// }

// fn resolve_names_stmt(
//     gamma: Gamma,
//     mode: Mode,
//     stmt: Rc<Stmt>,
//     ctx: &mut StaticsContext,
//     add_to_tyvar_gamma: bool,
// ) {
//     match &*stmt.kind {
//         StmtKind::InterfaceDef(..) => {}
//         StmtKind::Import(..) => {}
//         StmtKind::InterfaceImpl(ident, typ, statements) => {
//             let typ = ast_type_to_statics_type(ctx, typ.clone());

//             if let Some(interface_def) = ctx.interface_def_of_ident(ident) {
//                 for statement in statements {
//                     let StmtKind::FuncDef(pat, _args, _out, _body) = &*statement.kind else {
//                         continue;
//                     };
//                     let method_name = pat.kind.get_identifier_of_variable();
//                     if let Some(interface_method) =
//                         interface_def.methods.iter().find(|m| m.name == method_name)
//                     {
//                         let mut substitution = BTreeMap::new();
//                         substitution.insert("a".to_string(), typ.clone());

//                         let expected = interface_method.ty.clone().subst(
//                             gamma.clone(),
//                             Prov::Node(stmt.id),
//                             &substitution,
//                         );

//                         constrain(expected, TypeVar::from_node(ctx, pat.id));

//                         generate_constraints_stmt(
//                             gamma.clone(),
//                             Mode::Syn,
//                             statement.clone(),
//                             ctx,
//                             false,
//                         );
//                     } else {
//                         ctx.interface_impl_extra_method
//                             .entry(stmt.id)
//                             .or_default()
//                             .push(statement.id);
//                     }
//                 }
//                 for interface_method in interface_def.methods {
//                     if !statements.iter().any(|stmt| match &*stmt.kind {
//                         StmtKind::FuncDef(pat, _args, _out, _body) => {
//                             pat.kind.get_identifier_of_variable() == interface_method.name
//                         }
//                         _ => false,
//                     }) {
//                         ctx.interface_impl_missing_method
//                             .entry(stmt.id)
//                             .or_default()
//                             .push(interface_method.name.clone());
//                     }
//                 }
//             } else {
//                 ctx.unbound_interfaces.insert(stmt.id);
//             }
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
//             generate_constraints_expr(gamma, mode, expr.clone(), ctx);
//         }
//         StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
//             let ty_pat = TypeVar::from_node(ctx, pat.id);

//             generate_constraints_expr(
//                 gamma.clone(),
//                 Mode::Ana { expected: ty_pat },
//                 expr.clone(),
//                 ctx,
//             );

//             if let Some(ty_ann) = ty_ann {
//                 let ty_ann = ast_type_to_statics_type(ctx, ty_ann.clone());
//                 gamma.add_polys(&ty_ann);
//                 generate_constraints_pat(gamma, Mode::Ana { expected: ty_ann }, pat.clone(), ctx)
//             } else {
//                 generate_constraints_pat(gamma, Mode::Syn, pat.clone(), ctx)
//             };
//         }
//         StmtKind::Set(lhs, rhs) => {
//             let ty_lhs = TypeVar::from_node(ctx, lhs.id);
//             generate_constraints_expr(gamma.clone(), Mode::Syn, lhs.clone(), ctx);
//             let ty_rhs = TypeVar::from_node(ctx, rhs.id);
//             generate_constraints_expr(gamma, Mode::Syn, rhs.clone(), ctx);
//             constrain(ty_lhs, ty_rhs);
//         }
//         StmtKind::FuncDef(name, args, out_annot, body) => {
//             let func_node_id = stmt.id;
//             let ty_pat = TypeVar::from_node(ctx, name.id);

//             let func_name = name.kind.get_identifier_of_variable();

//             // TODO this needs a better explanation
//             if add_to_tyvar_gamma {
//                 gamma.extend(name.kind.get_identifier_of_variable(), ty_pat.clone());
//                 gamma.extend_declaration(
//                     func_name,
//                     Resolution::FreeFunction(stmt.id, name.kind.get_identifier_of_variable()),
//                 );
//             } else {
//                 gamma.extend_declaration(func_name.clone(), Resolution::InterfaceMethod(func_name));
//             }

//             let body_gamma = gamma.new_scope();
//             let ty_func = generate_constraints_func_helper(
//                 ctx,
//                 func_node_id,
//                 body_gamma,
//                 args,
//                 out_annot,
//                 body,
//             );

//             constrain(ty_pat, ty_func);
//         }
//     }
// }

// fn resolve_names_pat(gamma: Gamma, mode: Mode, pat: Rc<Pat>, ctx: &mut StaticsContext) {
//     let ty_pat = TypeVar::from_node(ctx, pat.id);
//     match mode {
//         Mode::Syn => (),
//         Mode::Ana { expected } => constrain(expected, ty_pat.clone()),
//     };
//     match &*pat.kind {
//         PatKind::Wildcard => (),
//         PatKind::Unit => {
//             constrain(ty_pat, TypeVar::make_unit(Prov::Node(pat.id)));
//         }
//         PatKind::Int(_) => {
//             constrain(ty_pat, TypeVar::make_int(Prov::Node(pat.id)));
//         }
//         PatKind::Float(_) => {
//             constrain(ty_pat, TypeVar::make_float(Prov::Node(pat.id)));
//         }
//         PatKind::Bool(_) => {
//             constrain(ty_pat, TypeVar::make_bool(Prov::Node(pat.id)));
//         }
//         PatKind::Str(_) => {
//             constrain(ty_pat, TypeVar::make_string(Prov::Node(pat.id)));
//         }
//         PatKind::Var(identifier) => {
//             // letrec: extend context with id and type before analyzing against said type
//             gamma.extend(identifier.clone(), ty_pat);
//             gamma.extend_declaration(identifier.clone(), Resolution::Var(pat.id));
//         }
//         PatKind::Variant(tag, data) => {
//             let ty_data = match data {
//                 Some(data) => TypeVar::from_node(ctx, data.id),
//                 None => TypeVar::make_unit(Prov::VariantNoData(Box::new(Prov::Node(pat.id)))),
//             };
//             let mut substitution = BTreeMap::new();
//             let ty_enum_instance = {
//                 let enum_def = ctx.enum_def_of_variant(tag);

//                 if let Some(enum_def) = enum_def {
//                     let nparams = enum_def.params.len();
//                     let mut params = vec![];
//                     for i in 0..nparams {
//                         params.push(TypeVar::fresh(
//                             ctx,
//                             Prov::InstantiateUdtParam(Box::new(Prov::Node(pat.id)), i as u8),
//                         ));
//                         substitution.insert(enum_def.params[i].clone(), params[i].clone());
//                     }
//                     let def_type = TypeVar::make_def_instance(
//                         Prov::UdtDef(Box::new(Prov::Node(pat.id))),
//                         enum_def.name,
//                         params,
//                     );

//                     let variant_def = enum_def.variants.iter().find(|v| v.ctor == *tag).unwrap();
//                     let variant_data_ty = variant_def.data.clone().subst(
//                         gamma.clone(),
//                         Prov::Node(pat.id),
//                         &substitution,
//                     );
//                     constrain(ty_data.clone(), variant_data_ty);

//                     def_type
//                 } else {
//                     panic!("variant not found");
//                 }
//             };

//             constrain(ty_pat, ty_enum_instance);
//             if let Some(data) = data {
//                 generate_constraints_pat(gamma, Mode::Ana { expected: ty_data }, data.clone(), ctx)
//             };
//         }
//         PatKind::Tuple(pats) => {
//             let tys_elements = pats
//                 .iter()
//                 .map(|pat| TypeVar::fresh(ctx, Prov::Node(pat.id)))
//                 .collect();
//             constrain(
//                 ty_pat,
//                 TypeVar::make_tuple(tys_elements, Prov::Node(pat.id)),
//             );
//             for pat in pats {
//                 generate_constraints_pat(gamma.clone(), Mode::Syn, pat.clone(), ctx)
//             }
//         }
//     }
// }
