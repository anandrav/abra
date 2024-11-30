use crate::ast::{
    EnumDef, FileAst, ForeignFuncDecl, FuncDef, InterfaceDef, InterfaceImpl, NodeId, NodeMap,
    Sources, StructDef, TypeKind,
};
use crate::builtin::Builtin;
use crate::effects::EffectDesc;
use resolve::{resolve, scan_declarations};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
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

    // map from interface name to list of implementations
    pub(crate) interface_impls: BTreeMap<Rc<InterfaceDef>, Vec<Rc<InterfaceImpl>>>,
    // string constants (for bytecode translation)
    pub(crate) string_constants: HashMap<String, usize>,
    // dylibs (for bytecode translation)
    pub(crate) dylib_name_to_id: HashMap<PathBuf, usize>,
    // pub(crate) dylibs: Vec<PathBuf>,
    pub(crate) dylib_id_and_funcname_to_id: HashMap<(usize, String), usize>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) vars: HashMap<TypeProv, TypeVar>,
    // constraint: map from types to interfaces they must implement
    types_constrained_to_interfaces: BTreeMap<TypeVar, Vec<(Rc<InterfaceDef>, TypeProv)>>, // TODO: can't use TypeVar as key because it's mutable. Use a Prov instead?
    // constraint: map from types which must be structs to location of field access
    types_that_must_be_structs: BTreeMap<TypeVar, NodeId>, // TODO: can't use TypeVar as key because it's mutable. Use a Prov instead?

    // ERRORS

    // unbound variables
    unbound_vars: BTreeSet<NodeId>,

    // non-exhaustive matches
    nonexhaustive_matches: BTreeMap<NodeId, Vec<DeconstructedPat>>,
    redundant_matches: BTreeMap<NodeId, Vec<NodeId>>,
    // annotation needed
    annotation_needed: BTreeSet<NodeId>,
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
        match self.vars.get(&prov) {
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
    ForeignFunction(Rc<ForeignFuncDecl>, usize),
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
    Array,
    Polytype(NodeId),
    Builtin(Builtin),
    Effect(u16),
    Var(NodeId),
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
    // TODO: rename this to solve_constraints()
    result_of_constraint_solving(&mut ctx, node_map, sources)?;

    // pattern exhaustiveness and usefulness checking
    check_pattern_exhaustiveness_and_usefulness(&mut ctx, files, node_map, sources)?;

    Ok(ctx)
}
