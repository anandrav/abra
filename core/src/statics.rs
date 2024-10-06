use crate::ast::{NodeId, NodeMap, Sources, Stmt, Symbol, Toplevel};
use crate::builtin::Builtin;
use crate::effects::EffectStruct;
use declarations::{gather_definitions_toplevel, EnumDef, InterfaceDef, InterfaceImpl, StructDef};
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;
use typecheck::{generate_constraints_toplevel, result_of_constraint_solving, SolvedType, TypeVar};

mod declarations;
mod exhaustiveness;
mod typecheck;

pub(crate) use typecheck::{ty_fits_impl_ty, Monotype};
// TODO: Provs are an implementation detail, they should NOT be exported
pub(crate) use typecheck::Prov as TypeProv;
pub(crate) use typecheck::SolvedType as Type;

pub(crate) use declarations::StructField;

use exhaustiveness::{result_of_additional_analysis, DeconstructedPat};

#[derive(Default, Debug)]
pub(crate) struct StaticsContext {
    // effects
    effects: Vec<EffectStruct>,

    // DECLARATIONS

    // new declaration stuff
    pub(crate) global_namespace: Namespace,

    // enum definitions
    pub(crate) enum_defs: HashMap<Symbol, EnumDef>,
    // map from variant names to enum names
    variants_to_enum: HashMap<Symbol, Symbol>,
    // struct definitions
    pub(crate) struct_defs: HashMap<Symbol, StructDef>,
    // function definition locations
    pub(crate) fun_defs: HashMap<Symbol, Rc<Stmt>>,
    // interface definitions
    interface_defs: HashMap<Symbol, InterfaceDef>,
    // map from methods to interface names
    pub(crate) method_to_interface: HashMap<Symbol, Symbol>,
    // map from interface name to list of implementations
    pub(crate) interface_impls: BTreeMap<Symbol, Vec<InterfaceImpl>>,

    // BOOKKEEPING

    // name resolutions
    pub(crate) name_resolutions: HashMap<NodeId, Resolution>,

    // string constants
    pub(crate) string_constants: HashMap<String, usize>,

    // TYPE CHECKING

    // unification variables (skolems) which must be solved
    pub(crate) vars: HashMap<TypeProv, TypeVar>,
    // map from types to interfaces they have been constrained to
    types_constrained_to_interfaces: BTreeMap<TypeVar, Vec<(Symbol, TypeProv)>>,
    // types that must be a struct because there was a field access
    types_that_must_be_structs: BTreeMap<TypeVar, NodeId>,

    // ERRORS

    // unbound variables
    unbound_vars: BTreeSet<NodeId>,
    unbound_interfaces: BTreeSet<NodeId>,
    // multiple definitions
    multiple_udt_defs: BTreeMap<Symbol, Vec<NodeId>>,
    multiple_interface_defs: BTreeMap<Symbol, Vec<NodeId>>,
    // interface implementations
    multiple_interface_impls: BTreeMap<Symbol, Vec<NodeId>>,
    interface_impl_for_instantiated_ty: Vec<NodeId>,
    interface_impl_extra_method: BTreeMap<NodeId, Vec<NodeId>>,
    interface_impl_missing_method: BTreeMap<NodeId, Vec<String>>,
    // non-exhaustive matches
    nonexhaustive_matches: BTreeMap<NodeId, Vec<DeconstructedPat>>,
    redundant_matches: BTreeMap<NodeId, Vec<NodeId>>,
    // annotation needed
    annotation_needed: BTreeSet<NodeId>,
    // field not an identifier
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

    fn enum_def_of_variant(&self, variant: &Symbol) -> Option<EnumDef> {
        let enum_name = self.variants_to_enum.get(variant)?;
        self.enum_defs.get(enum_name).cloned()
    }

    fn interface_def_of_ident(&self, ident: &Symbol) -> Option<InterfaceDef> {
        self.interface_defs.get(ident).cloned()
    }

    fn variants_of_enum(&self, enumt: &Symbol) -> Vec<Symbol> {
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

#[derive(Clone, Debug, Default)]
pub struct Namespace {
    namespaces: HashMap<String, Namespace>,
    declarations: HashMap<String, Declaration>,
}

#[derive(Debug, Clone)]
pub(crate) enum Declaration {
    Enum(EnumDef),
    Struct(StructDef),
    FreeFunction(Rc<Stmt>),
    Interface(InterfaceDef),
}

#[derive(Debug, Clone)]
pub(crate) enum Resolution {
    Var(NodeId),
    FreeFunction(NodeId, Symbol),
    InterfaceMethod(Symbol),
    StructCtor(u16),
    VariantCtor(u16, u16),
    Builtin(Builtin),
    Effect(u16),
}

// main function that performs typechecking (as well as name resolution beforehand)
pub(crate) fn analyze(
    effects: &[EffectStruct],
    toplevels: &Vec<Rc<Toplevel>>,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<StaticsContext, String> {
    let mut ctx = StaticsContext::new(effects.to_owned()); // TODO: to_owned necessary?

    // TODO: Gamma should be an implementation detail of typechecker
    let tyctx = typecheck::Gamma::empty();
    // declarations
    for parse_tree in toplevels {
        gather_definitions_toplevel(&mut ctx, tyctx.clone(), parse_tree.clone());
    }

    // typechecking
    for parse_tree in toplevels {
        generate_constraints_toplevel(tyctx.clone(), parse_tree.clone(), &mut ctx);
    }
    result_of_constraint_solving(&mut ctx, node_map, sources)?;

    // pattern exhaustiveness and usefulness checking
    result_of_additional_analysis(&mut ctx, toplevels, node_map, sources)?;

    Ok(ctx)
}
