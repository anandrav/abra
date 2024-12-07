use crate::ast::{
    EnumDef, FileAst, ForeignFuncDecl, FuncDef, Identifier, InterfaceDef, InterfaceImpl, NodeId,
    NodeMap, Sources, StructDef, TypeKind,
};
use crate::builtin::Builtin;
use crate::effects::EffectDesc;
use resolve::{resolve, scan_declarations};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter, Write};
use std::path::PathBuf;
use std::rc::Rc;
use typecheck::{generate_constraints_file, result_of_constraint_solving, SolvedType, TypeVar};

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
    pub(crate) interface_impls: BTreeMap<Rc<InterfaceDef>, Vec<Rc<InterfaceImpl>>>,

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
    InterfaceDef(Rc<InterfaceDef>),
    InterfaceMethod {
        iface_def: Rc<InterfaceDef>,
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
    Unconstrained {
        node_id: NodeId,
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
    // check_errors(&ctx, node_map, sources)?; // TODO: just check errors once at the end of static analysis (before bytecode generation)

    // typechecking
    for file in files {
        generate_constraints_file(file.clone(), &mut ctx);
    }
    // TODO: rename this to solve_constraints()
    result_of_constraint_solving(&mut ctx, node_map, sources)?;

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

            Error::Unconstrained { node_id } => {
                let span = node_map.get(node_id).unwrap().span();
                span.display(
                    &mut err_string,
                    sources,
                    "Can't solve type of this. Try adding a type annotation.",
                );
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
