use crate::ast::{
    EnumDef, FileAst, FuncDef, InterfaceDef, InterfaceImpl, NodeId, NodeMap, Sources, StructDef,
    TypeKind,
};
use crate::builtin::Builtin;
use crate::effects::EffectStruct;
use resolve::{resolve, scan_declarations};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Display, Formatter};
use std::rc::Rc;
use typecheck::{generate_constraints_file, result_of_constraint_solving, SolvedType, TypeVar};

mod pat_exhaustiveness;
mod resolve;
pub(crate) mod typecheck;

pub(crate) use typecheck::{ty_fits_impl_ty, Monotype};
// TODO: Provs are an implementation detail, they should NOT be exported
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

use pat_exhaustiveness::{check_pattern_exhaustiveness_and_usefulness, DeconstructedPat};

#[derive(Default, Debug)]
pub(crate) struct StaticsContext {
    // effects
    effects: Vec<EffectStruct>,
    _node_map: NodeMap,
    _sources: Sources,

    global_namespace: Namespace,
    // This maps any identifier in the program to the declaration it resolves to.
    pub(crate) resolution_map: HashMap<NodeId, Declaration>,

    // BOOKKEEPING

    // map from methods to interface names
    pub(crate) method_to_interface: HashMap<String, String>, // TODO: can't use Strings here
    // map from interface name to list of implementations
    pub(crate) interface_impls: BTreeMap<String, Vec<Rc<InterfaceImpl>>>, // TODO can't use String for key. Use Rc<InterfaceDef>
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
    fn new(effects: Vec<EffectStruct>, node_map: NodeMap, sources: Sources) -> Self {
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

    // fn interface_def_of_ident(&self, ident: &String) -> Option<InterfaceDef_OLD> {
    //     self.interface_defs.get(ident).cloned()
    // }

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
    InterfaceMethod {
        iface_def: Rc<InterfaceDef>,
        method: u16,
    },
    Enum(Rc<EnumDef>),
    EnumVariant {
        enum_def: Rc<EnumDef>,
        variant: u16,
    },
    Struct(Rc<StructDef>),
    Array,
    Builtin(Builtin),
    Effect(u16),
    Var(NodeId),
}

impl Declaration {
    pub fn to_bytecode_resolution(&self) -> BytecodeResolution {
        match self {
            Declaration::Var(node_id) => BytecodeResolution::Var(*node_id),
            Declaration::FreeFunction(f) => {
                BytecodeResolution::FreeFunction(f.clone(), f.name.v.clone())
            }
            Declaration::InterfaceDef(_) => panic!(), // TODO: remove panic
            Declaration::InterfaceMethod { iface_def, method } => {
                let name = &iface_def.props[*method as usize].name;
                BytecodeResolution::InterfaceMethod(name.v.clone())
            }
            Declaration::Enum(..) => {
                panic!() // TODO: remove panic
            }
            Declaration::EnumVariant { enum_def, variant } => {
                let data = &enum_def.variants[*variant as usize].data;
                let arity = match data {
                    None => 0,
                    Some(ty) => match &*ty.kind {
                        TypeKind::Poly(..)
                        | TypeKind::Identifier(_)
                        | TypeKind::Ap(..)
                        | TypeKind::Unit
                        | TypeKind::Int
                        | TypeKind::Float
                        | TypeKind::Bool
                        | TypeKind::Str
                        | TypeKind::Function(..) => 1,
                        TypeKind::Tuple(elems) => elems.len(),
                    },
                } as u16;
                BytecodeResolution::VariantCtor(*variant, arity)
            }
            Declaration::Struct(struct_def) => {
                let nargs = struct_def.fields.len() as u16;
                BytecodeResolution::StructCtor(nargs)
            }
            Declaration::Array => {
                panic!();
            }
            Declaration::Builtin(b) => BytecodeResolution::Builtin(*b),
            Declaration::Effect(e) => BytecodeResolution::Effect(*e),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum BytecodeResolution {
    Var(NodeId),
    FreeFunction(Rc<FuncDef>, String), // TODO: String bad unless fully qualified!
    InterfaceMethod(String),           // TODO: String bad unless fully qualified!
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
