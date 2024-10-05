use std::{fmt, rc::Rc};

use crate::ast::{Node, NodeId, Stmt, StmtKind, Symbol, Toplevel, TypeDefKind, TypeKind};

use super::{Resolution, StaticsContext, TypeVar};

// TODO: constrain, Gamma, Prov should be implementation details
// TODO: others should probably be implementation details too
use super::typecheck::{
    ast_type_to_statics_type, ast_type_to_statics_type_interface, constrain, Gamma, Prov,
};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct AdtDef {
    pub(crate) name: Symbol,
    pub(crate) params: Vec<Symbol>,
    pub(crate) variants: Vec<Variant>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Variant {
    pub(crate) ctor: Symbol,
    pub(crate) data: TypeVar,
}

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.ctor, self.data)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructDef {
    pub(crate) name: Symbol,
    pub(crate) params: Vec<Symbol>,
    pub(crate) fields: Vec<StructField>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct StructField {
    pub(crate) name: Symbol,
    pub(crate) ty: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceDef {
    pub(crate) name: Symbol,
    pub(crate) methods: Vec<InterfaceDefMethod>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceImpl {
    pub(crate) name: Symbol,
    pub(crate) typ: TypeVar,
    pub(crate) methods: Vec<InterfaceImplMethod>,
    pub(crate) location: NodeId,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceDefMethod {
    pub(crate) name: Symbol,
    pub(crate) ty: TypeVar,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct InterfaceImplMethod {
    pub(crate) name: Symbol,
    pub(crate) method_location: NodeId,
    pub(crate) identifier_location: NodeId,
}

pub(crate) fn gather_definitions_toplevel(
    ctx: &mut StaticsContext,
    gamma: Gamma,
    toplevel: Rc<Toplevel>,
) {
    for statement in toplevel.statements.iter() {
        gather_definitions_stmt(ctx, gamma.clone(), statement.clone());
    }
}

fn gather_definitions_stmt(ctx: &mut StaticsContext, gamma: Gamma, stmt: Rc<Stmt>) {
    match &*stmt.stmtkind {
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

            if typ.is_instantiated_adt() {
                ctx.interface_impl_for_instantiated_adt.push(stmt.id);
            }

            let methods = stmts
                .iter()
                .map(|stmt| match &*stmt.stmtkind {
                    StmtKind::FuncDef(pat, _, _, _) => {
                        let ident = pat.patkind.get_identifier_of_variable();
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
            TypeDefKind::Adt(ident, params, variants) => {
                if let Some(adt_def) = ctx.adt_defs.get(ident) {
                    let entry = ctx.multiple_udt_defs.entry(ident.clone()).or_default();
                    entry.push(adt_def.location);
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
                    ctx.variants_to_adt.insert(v.ctor.clone(), ident.clone());
                }
                let mut defparams = vec![];
                for p in params {
                    let TypeKind::Poly(ident, _) = &*p.typekind else {
                        panic!("expected poly type for ADT def param")
                    };
                    defparams.push(ident.clone());
                }
                ctx.adt_defs.insert(
                    ident.clone(),
                    AdtDef {
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
                        panic!("expected poly type for ADT def param")
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
            let name = name.patkind.get_identifier_of_variable();
            ctx.fun_defs.insert(name.clone(), stmt.clone());
            gamma.extend(name.clone(), TypeVar::from_node(ctx, name_id));
            gamma.extend_declaration(name.clone(), Resolution::FreeFunction(stmt.id, name));
        }
        StmtKind::Set(..) => {}
    }
}
