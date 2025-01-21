use crate::ast::{
    EnumDef, FileAst, ForeignFuncDecl, FuncDef, Identifier, InterfaceDecl, InterfaceImpl, NodeId,
    NodeMap, Sources, StructDef, TypeKind,
};
use crate::builtin::Builtin;
use crate::effects::EffectDesc;
use crate::statics::typecheck::Prov;
use resolve::{resolve, scan_declarations};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter, Write};
use std::path::PathBuf;
use std::rc::Rc;
use typecheck::{
    fmt_conflicting_types, generate_constraints_file, result_of_constraint_solving, PotentialType,
    SolvedType, TypeKey, TypeVar,
};

mod pat_exhaustiveness;
mod resolve;
pub(crate) mod typecheck;

pub(crate) use typecheck::ty_fits_impl_ty;
// TODO: Provs are an implementation detail, they should NOT be exported
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

pub use typecheck::Monotype;

use pat_exhaustiveness::{check_pattern_exhaustiveness_and_usefulness, DeconstructedPat};

#[derive(Default, Debug)]
pub(crate) struct StaticsContext {
    // effects
    effects: Vec<EffectDesc>,
    _node_map: NodeMap,
    _sources: Sources,

    pub(crate) global_namespace: Namespace,
    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,

    // BOOKKEEPING

    // map from interface name to list of its implementations
    pub(crate) interface_impls: BTreeMap<Rc<InterfaceDecl>, Vec<Rc<InterfaceImpl>>>,

    // string constants (for bytecode translation)
    pub(crate) string_constants: HashMap<String, usize>,
    // dylibs (for bytecode translation)
    // pub(crate) dylibs: BTreeSet<PathBuf>,
    pub(crate) dylib_to_funcs: BTreeMap<PathBuf, BTreeSet<String>>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) unifvars: HashMap<TypeProv, TypeVar>,
    // constraint: map from types to interfaces they must implement
    // types_constrained_to_interfaces: BTreeMap<TypeVar, Vec<(Rc<InterfaceDef>, TypeProv)>>, // TODO: can't use TypeVar as key because it's mutable. Use a Prov instead?
    // constraint: map from types which must be structs to location of field access
    types_that_must_be_structs: BTreeMap<TypeVar, NodeId>, // TODO: can't use TypeVar as key because it's mutable. Use a Prov instead?

    // ERRORS
    errors: Vec<Error>,
}

impl StaticsContext {
    fn new(effects: Vec<EffectDesc>, node_map: NodeMap, sources: Sources) -> Self {
        let mut ctx = Self {
            effects,
            _node_map: node_map,
            _sources: sources,
            ..Default::default()
        };

        // TODO: this string constant needs to come from builtins, not be hardcoded
        ctx.string_constants.entry("\n".into()).or_insert(0);
        ctx
    }

    pub(crate) fn solution_of_node(&self, id: NodeId) -> Option<SolvedType> {
        let prov = TypeProv::Node(id);
        match self.unifvars.get(&prov) {
            Some(unifvar) => unifvar.solution(),
            None => None,
        }
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct Namespace {
    pub(crate) declarations: BTreeMap<String, Declaration>,
    pub(crate) namespaces: BTreeMap<String, Rc<Namespace>>,
}

impl Display for Namespace {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        // indent for each level
        fn fmt_tree(tree: &Namespace, f: &mut Formatter, indent: usize) -> fmt::Result {
            for ident in tree.declarations.keys() {
                writeln!(f, "{:indent$}{}", "", ident)?;
            }
            for (ident, subtree) in &tree.namespaces {
                writeln!(f, "{:indent$}{}", "", ident)?;
                fmt_tree(subtree, f, indent + 2)?;
            }
            Ok(())
        }
        fmt_tree(self, f, 0)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Declaration {
    FreeFunction(Rc<FuncDef>, String),
    ForeignFunction {
        decl: Rc<ForeignFuncDecl>,
        libname: PathBuf,
        symbol: String,
    },
    InterfaceDef(Rc<InterfaceDecl>),
    InterfaceMethod {
        iface_def: Rc<InterfaceDecl>,
        method: u16,
        fully_qualified_name: String,
    },
    Enum(Rc<EnumDef>),
    EnumVariant {
        enum_def: Rc<EnumDef>,
        variant: u16,
    },
    Struct(Rc<StructDef>),
    ForeignType(Identifier),
    Array,
    Polytype(NodeId),
    Builtin(Builtin),
    Effect(u16),
    Var(NodeId),
}

#[derive(Debug)]
pub(crate) enum Error {
    // resolution phase
    UnboundVariable {
        node_id: NodeId,
    },
    // typechecking phase
    UnconstrainedUnifvar {
        node_id: NodeId,
    },
    ConflictingUnifvar {
        types: BTreeMap<TypeKey, PotentialType>,
    },
    ConflictingTypes {
        ty1: PotentialType,
        ty2: PotentialType,
    },
    MemberAccessNeedsAnnotation {
        node_id: NodeId,
    },
    BadFieldAccess {
        node_id: NodeId,
        typ: SolvedType,
    },
    // pattern matching exhaustiveness check
    NonexhaustiveMatch {
        expr_id: NodeId,
        missing: Vec<DeconstructedPat>,
    },
    RedundantArms {
        expr_id: NodeId,
        redundant_arms: Vec<NodeId>,
    },
}

// main function that performs typechecking (as well as name resolution beforehand)
pub(crate) fn analyze(
    effects: &[EffectDesc],
    files: &Vec<Rc<FileAst>>,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<StaticsContext, String> {
    let mut ctx = StaticsContext::new(effects.to_owned(), node_map.clone(), sources.clone()); // TODO: to_owned necessary?

    // scan declarations across all files
    scan_declarations(&mut ctx, files.clone());

    // resolve all imports and identifiers
    resolve(&mut ctx, files.clone());

    // typechecking
    for file in files {
        generate_constraints_file(file.clone(), &mut ctx);
    }
    result_of_constraint_solving(&mut ctx);

    // pattern exhaustiveness and usefulness checking
    check_pattern_exhaustiveness_and_usefulness(&mut ctx, files);
    check_errors(&ctx, node_map, sources)?;

    Ok(ctx)
}

pub(crate) fn check_errors(
    ctx: &StaticsContext,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<(), String> {
    if ctx.errors.is_empty() {
        return Ok(());
    }

    let mut err_string = String::new();

    for error in &ctx.errors {
        err_string.push_str(&error.show(ctx, node_map, sources));
    }

    Err(err_string)
}

impl Error {
    fn show(&self, ctx: &StaticsContext, node_map: &NodeMap, sources: &Sources) -> String {
        let mut err_string = String::new();
        match self {
            Error::UnboundVariable { node_id: expr_id } => {
                err_string.push_str("This variable is unbound:\n");
                let span = node_map.get(expr_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }

            Error::UnconstrainedUnifvar { node_id } => {
                let span = node_map.get(node_id).unwrap().span();
                span.display(
                    &mut err_string,
                    sources,
                    "Can't solve type of this. Try adding a type annotation.",
                );
            }
            Error::ConflictingUnifvar { types } => {
                err_string.push_str("Conflicting types: ");
                let mut type_conflict: Vec<PotentialType> = types.values().cloned().collect();
                type_conflict.sort_by_key(|ty| ty.provs().borrow().len());

                fmt_conflicting_types(&type_conflict, &mut err_string).unwrap();
                writeln!(err_string).unwrap();
                for ty in type_conflict {
                    err_string.push('\n');
                    match &ty {
                        PotentialType::Poly(_, _, _) => {
                            err_string.push_str("Sources of generic type:\n")
                        }
                        PotentialType::Nominal(_, nominal, params) => {
                            let _ = write!(err_string, "Sources of type {}<", nominal.name());
                            for (i, param) in params.iter().enumerate() {
                                if i != 0 {
                                    err_string.push_str(", ");
                                }
                                let _ = writeln!(err_string, "{param}");
                            }
                            err_string.push_str(">\n");
                        }
                        PotentialType::Unit(_) => err_string.push_str("Sources of void:\n"),
                        PotentialType::Int(_) => err_string.push_str("Sources of int:\n"),
                        PotentialType::Float(_) => err_string.push_str("Sources of float:\n"),
                        PotentialType::Bool(_) => err_string.push_str("Sources of bool:\n"),
                        PotentialType::String(_) => err_string.push_str("Sources of string:\n"),
                        PotentialType::Function(_, args, _) => {
                            let _ = writeln!(
                                err_string,
                                "Sources of function with {} arguments",
                                args.len()
                            );
                        }
                        PotentialType::Tuple(_, elems) => {
                            let _ = writeln!(
                                err_string,
                                "Sources of tuple with {} elements",
                                elems.len()
                            );
                        }
                    };
                    let provs = ty.provs().borrow();
                    let mut provs_vec = provs.iter().collect::<Vec<_>>();
                    provs_vec.sort_by_key(|prov| match prov {
                        Prov::Builtin(_) => 0,
                        Prov::Node(id) => node_map.get(id).unwrap().span().lo,
                        Prov::InstantiatePoly(_, _ident) => 2,
                        Prov::FuncArg(_, _) => 3,
                        Prov::FuncOut(_) => 4,
                        Prov::VariantNoData(_) => 7,
                        Prov::UdtDef(_) => 8,
                        Prov::InstantiateUdtParam(_, _) => 9,
                        Prov::ListElem(_) => 10,
                        Prov::BinopLeft(_) => 11,
                        Prov::BinopRight(_) => 12,
                        Prov::StructField(..) => 14,
                        Prov::IndexAccess => 15,
                        Prov::Effect(_) => 16,
                    });
                    for cause in provs_vec {
                        write_prov_to_err_string(&mut err_string, cause, node_map, sources);
                    }
                }
                writeln!(err_string).unwrap();
            }
            Error::ConflictingTypes { ty1, ty2 } => {
                err_string.push_str(&format!("Type conflict. Got type {}:\n", ty1));
                let provs1 = ty1.provs().borrow();
                let cause1 = provs1.iter().next().unwrap();
                write_prov_to_err_string(&mut err_string, cause1, node_map, sources);
                err_string.push_str(&format!("But also got type {}:\n", ty2));
                let provs2 = ty2.provs().borrow();
                let cause2 = provs2.iter().next().unwrap();
                write_prov_to_err_string(&mut err_string, cause2, node_map, sources);
                err_string.push('\n');
            }
            Error::MemberAccessNeedsAnnotation { node_id } => {
                let span = node_map.get(node_id).unwrap().span();
                span.display(
                    &mut err_string,
                    sources,
                    "Can't perform member access without knowing type. Try adding a type annotation.",
                );
            }
            Error::BadFieldAccess { node_id, typ } => {
                let _ = writeln!(
                    err_string,
                    "Can't access member variable because type '{}' is not a struct.",
                    typ
                );
                let span = node_map.get(node_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }

            Error::NonexhaustiveMatch { expr_id, missing } => {
                let span = node_map.get(expr_id).unwrap().span();
                span.display(
                    &mut err_string,
                    sources,
                    "This match expression doesn't cover every possibility:\n",
                );
                err_string.push_str("\nThe following cases are missing:\n");
                for pat in missing {
                    let _ = writeln!(err_string, "\t`{pat}`\n");
                }
            }
            Error::RedundantArms {
                expr_id,
                redundant_arms,
            } => {
                let span = node_map.get(expr_id).unwrap().span();
                span.display(
                    &mut err_string,
                    sources,
                    "This match expression has redundant cases:\n",
                );
                err_string.push_str("\nTry removing these cases\n");
                for pat in redundant_arms {
                    let span = node_map.get(pat).unwrap().span();
                    span.display(&mut err_string, sources, "");
                }
            }
        };
        err_string
    }
}

// TODO: This sucks so bad...
fn write_prov_to_err_string(
    err_string: &mut String,
    cause: &Prov,
    node_map: &NodeMap,
    sources: &Sources,
) {
    match cause {
        Prov::Builtin(builtin) => {
            let s = builtin.name();
            let _ = writeln!(err_string, "The builtin function {s}");
        }
        Prov::Effect(u16) => {
            let _ = writeln!(err_string, "The effect {u16}");
        }
        Prov::Node(id) => {
            let span = node_map.get(id).unwrap().span();
            span.display(err_string, sources, "");
        }
        Prov::InstantiatePoly(_, ident) => {
            let _ = writeln!(err_string, "The instantiation of polymorphic type {ident}");
        }
        Prov::FuncArg(prov, n) => {
            match prov.as_ref() {
                Prov::Builtin(builtin) => {
                    let s = builtin.name();
                    let n = n + 1; // readability
                    let _ = writeln!(err_string, "--> The #{n} argument of function '{s}'");
                }
                Prov::Node(id) => {
                    let span = node_map.get(id).unwrap().span();
                    span.display(
                        err_string,
                        sources,
                        &format!("The #{n} argument of this function"),
                    );
                }
                _ => unreachable!(),
            }
        }
        Prov::FuncOut(prov) => match prov.as_ref() {
            Prov::Builtin(builtin) => {
                let s = builtin.name();
                let _ = writeln!(
                    err_string,
                    "
                    --> The output of the builtin function '{s}'"
                );
            }
            Prov::Node(id) => {
                let span = node_map.get(id).unwrap().span();
                span.display(err_string, sources, "The output of this function");
            }
            _ => unreachable!(),
        },
        Prov::BinopLeft(inner) => {
            err_string.push_str("The left operand of operator\n");
            if let Prov::Node(id) = **inner {
                let span = node_map.get(&id).unwrap().span();
                span.display(err_string, sources, "");
            }
        }
        Prov::BinopRight(inner) => {
            err_string.push_str("The left operand of this operator\n");
            if let Prov::Node(id) = **inner {
                let span = node_map.get(&id).unwrap().span();
                span.display(err_string, sources, "");
            }
        }
        Prov::ListElem(_) => {
            err_string.push_str("The element of some list");
        }
        Prov::UdtDef(_prov) => {
            err_string.push_str("Some type definition");
        }
        Prov::InstantiateUdtParam(_, _) => {
            err_string.push_str("Some instance of an Enum's variant");
        }
        Prov::VariantNoData(_prov) => {
            err_string.push_str("The data of some Enum variant");
        }
        Prov::StructField(field, ty) => {
            let _ = writeln!(err_string, "The field {field} of the struct {ty}");
        }
        Prov::IndexAccess => {
            let _ = writeln!(err_string, "Index for array access");
        }
    }
}
