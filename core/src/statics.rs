use crate::ast::{EnumDef, FileAst, FuncDef, InterfaceDef, NodeId, NodeMap, Sources, StructDef};
use crate::builtin::Builtin;
use crate::effects::EffectStruct;
use resolve::{
    resolve, scan_declarations, EnumDef_OLD, InterfaceDef_OLD, InterfaceImpl_OLD, StructDef_OLD,
};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;
use typecheck::{generate_constraints_file, result_of_constraint_solving, SolvedType, TypeVar};

mod pat_exhaustiveness;
mod resolve;
mod typecheck;

pub(crate) use typecheck::{ty_fits_impl_ty, Monotype};
// TODO: Provs are an implementation detail, they should NOT be exported
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

pub(crate) use resolve::StructField_OLD;

use pat_exhaustiveness::{result_of_additional_analysis, DeconstructedPat};

#[derive(Default, Debug)]
pub(crate) struct StaticsContext {
    // effects
    effects: Vec<EffectStruct>,

    // DECLARATIONS

    // new declaration stuff
    global_namespace: Namespace,

    // TODO this should all be replaced by Declarations in the SymbolTable
    // TODO: just attempt remove them one by one. Use NodeId instead of String
    // enum definitions
    pub(crate) enum_defs: HashMap<String, EnumDef_OLD>,
    // map from variant names to enum names
    variants_to_enum: HashMap<String, String>,
    // struct definitions
    pub(crate) struct_defs: HashMap<String, StructDef_OLD>,
    // function definition locations
    // pub(crate) fun_defs: HashMap<String, Rc<FuncDef>>,
    // interface definitions
    interface_defs: HashMap<String, InterfaceDef_OLD>,
    // map from methods to interface names
    pub(crate) method_to_interface: HashMap<String, String>,
    // map from interface name to list of implementations
    pub(crate) interface_impls: BTreeMap<String, Vec<InterfaceImpl_OLD>>,

    // BOOKKEEPING

    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,
    pub(crate) resolution_map_OLD: HashMap<NodeId, Resolution_OLD>,
    // string constants (for bytecode translation)
    pub(crate) string_constants: HashMap<String, usize>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) vars: HashMap<TypeProv, TypeVar>,
    // constraint: map from types to interfaces they must implement
    types_constrained_to_interfaces: BTreeMap<TypeVar, Vec<(String, TypeProv)>>,
    // constraint: map from types which must be structs to location of field access
    types_that_must_be_structs: BTreeMap<TypeVar, NodeId>,

    // ERRORS

    // unbound variables
    unbound_vars: BTreeSet<NodeId>,
    unbound_interfaces: BTreeSet<NodeId>,
    // multiple definitions
    multiple_udt_defs: BTreeMap<String, Vec<NodeId>>,
    multiple_interface_defs: BTreeMap<String, Vec<NodeId>>,
    // interface implementations
    multiple_interface_impls: BTreeMap<String, Vec<NodeId>>,
    interface_impl_for_instantiated_ty: Vec<NodeId>,
    interface_impl_extra_method: BTreeMap<NodeId, Vec<NodeId>>,
    interface_impl_missing_method: BTreeMap<NodeId, Vec<String>>,
    // non-exhaustive matches
    nonexhaustive_matches: BTreeMap<NodeId, Vec<DeconstructedPat>>,
    redundant_matches: BTreeMap<NodeId, Vec<NodeId>>,
    // annotation needed
    annotation_needed: BTreeSet<NodeId>,
    // field not an String
    field_not_ident: BTreeSet<NodeId>,
}

impl StaticsContext {
    fn new(effects: Vec<EffectStruct>) -> Self {
        let mut ctx = Self {
            effects,
            ..Default::default()
        };

        // TODO this string constant needs to come from builtins, not be hardcoded
        ctx.string_constants.entry("\n".into()).or_insert(0);
        ctx
    }

    fn enum_def_of_variant(&self, variant: &String) -> Option<EnumDef_OLD> {
        let enum_name = self.variants_to_enum.get(variant)?;
        self.enum_defs.get(enum_name).cloned()
    }

    fn interface_def_of_ident(&self, ident: &String) -> Option<InterfaceDef_OLD> {
        self.interface_defs.get(ident).cloned()
    }

    fn variants_of_enum(&self, enumt: &String) -> Vec<String> {
        self.enum_defs
            .get(enumt)
            .unwrap()
            .variants
            .iter()
            .map(|v| v.ctor.clone())
            .collect()
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
struct Namespace {
    declarations: BTreeMap<String, Declaration>,
    namespaces: BTreeMap<String, Rc<Namespace>>,
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

// TODO: separation of concerns. storing number of arguments, tag, etc. because the bytecode translator needs it is kinda weird, maybe reconsider.
// Try to store more general information which the bytecode translator can then use to derive specific things it cares about.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Declaration {
    FreeFunction(Rc<FuncDef>),
    InterfaceDef(Rc<InterfaceDef>),
    InterfaceMethod { parent: Rc<InterfaceDef>, idx: u16 },
    EnumVariant { parent: Rc<EnumDef>, idx: u16 },
    Struct(Rc<StructDef>),
    Builtin(Builtin),
    Effect(u16),
    Var(NodeId),
}

// TODO: move this to translate_bytecode. Make a conversion function from Declaration/Resolution to this thing
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Resolution_OLD {
    Var(NodeId),
    FreeFunction(NodeId, String),
    InterfaceMethod(String),
    StructCtor(u16),
    VariantCtor(u16, u16),
    Builtin(Builtin),
    Effect(u16),
}

// main function that performs typechecking (as well as name resolution beforehand)
pub(crate) fn analyze(
    effects: &[EffectStruct],
    files: &Vec<Rc<FileAst>>,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<StaticsContext, String> {
    let mut ctx = StaticsContext::new(effects.to_owned()); // TODO: to_owned necessary?

    // TODO: don't create symbol_table here
    let tyctx = typecheck::SymbolTable_OLD::empty();

    // scan declarations across all files
    scan_declarations(&mut ctx, tyctx.clone(), files.clone());
    // resolve all imports and Strings
    resolve(&mut ctx, files.clone());

    println!("global namespace:\n{}", ctx.global_namespace);

    // typechecking
    for file in files {
        generate_constraints_file(tyctx.clone(), file.clone(), &mut ctx);
    }
    // TODO: rename this to solve_constraints()
    result_of_constraint_solving(&mut ctx, node_map, sources)?;

    // pattern exhaustiveness and usefulness checking
    // TODO: rename this function
    result_of_additional_analysis(&mut ctx, files, node_map, sources)?;

    Ok(ctx)
}
