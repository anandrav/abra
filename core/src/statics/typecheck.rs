use crate::ast::{
    ArgAnnotated, Expr, ExprKind, FileAst, Identifier, ItemKind, Node, NodeId, Pat, PatKind, Stmt,
    StmtKind, Type as AstType, TypeDefKind, TypeKind,
};
use crate::ast::{BinaryOperator, Item};
use crate::builtin::Builtin;
use crate::environment::Environment;
use core::panic;
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Display, Write};
use std::rc::Rc;

use super::{Declaration, EnumDef, Error, FuncDef, InterfaceDecl, StaticsContext, StructDef};

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TypeVar(UnionFindNode<TypeVarData>);

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TypeVarData {
    pub(crate) types: BTreeMap<TypeKey, PotentialType>,
    pub(crate) locked: bool,
}

impl TypeVarData {
    fn new() -> Self {
        Self {
            types: BTreeMap::new(),
            locked: false,
        }
    }

    fn singleton_solved(potential_type: PotentialType) -> Self {
        let mut types = BTreeMap::new();
        types.insert(potential_type.key(), potential_type);
        Self {
            types,
            locked: true,
        }
    }

    fn solution(&self) -> Option<SolvedType> {
        if self.types.len() == 1 {
            self.types.values().next().unwrap().solution()
        } else {
            None
        }
    }

    fn merge_data(first: Self, second: Self) -> Self {
        // assert!(!first.locked && !second.locked);

        let mut merged_types = Self {
            types: first.types,
            locked: false,
        };
        for (_key, t) in second.types {
            merged_types.extend(t);
        }
        merged_types
    }

    fn extend(&mut self, mut t_other: PotentialType) {
        let key = t_other.key();

        // accumulate provenances and constrain children to each other if applicable
        if let Some(t) = self.types.get_mut(&key) {
            match &mut t_other {
                PotentialType::Unit(other_provs)
                | PotentialType::Int(other_provs)
                | PotentialType::Float(other_provs)
                | PotentialType::Bool(other_provs)
                | PotentialType::String(other_provs) => t
                    .reasons()
                    .borrow_mut()
                    .extend(other_provs.borrow().clone()),
                PotentialType::Poly(other_provs, _, _interfaces) => t
                    .reasons()
                    .borrow_mut()
                    .extend(other_provs.borrow().clone()),
                PotentialType::Function(other_provs, args1, out1) => {
                    t.reasons()
                        .borrow_mut()
                        .extend(other_provs.borrow().clone());
                    if let PotentialType::Function(_, args2, out2) = t {
                        for (arg, arg2) in args1.iter().zip(args2.iter()) {
                            TypeVar::merge(arg.clone(), arg2.clone());
                        }
                        TypeVar::merge(out1.clone(), out2.clone());
                    }
                }
                PotentialType::Tuple(other_provs, elems1) => {
                    t.reasons()
                        .borrow_mut()
                        .extend(other_provs.borrow().clone());
                    if let PotentialType::Tuple(_, elems2) = t {
                        for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                            TypeVar::merge(elem.clone(), elem2.clone());
                        }
                    }
                }
                PotentialType::Nominal(other_provs, _, other_tys) => {
                    if let PotentialType::Nominal(_, _, tys) = t {
                        if tys.len() == other_tys.len() {
                            for (ty, other_ty) in tys.iter().zip(other_tys.iter()) {
                                TypeVar::merge(ty.clone(), other_ty.clone());
                            }
                        } else {
                            panic!("should be same length")
                        }
                        t.reasons()
                            .borrow_mut()
                            .extend(other_provs.borrow().clone());
                    } else {
                        panic!("should be Ap")
                    }
                }
            }
        } else {
            // potential conflict
            self.types.insert(key, t_other);
        }
    }
}

// *** NOT SURE WHICH ORDER THESE SHOULD BE DONE IN! ***
// TODO: Replace Provs here with a different type, "Reasons"
// TODO: make it so we are either
/*
1. constraining to TypeVars to each other, which unifies them
2. constraining a TypeVar to a SolvedType, which just adds info to the TypeVar's data
3. constraining two SolvedType
- if we constrain two SolvedType and they conflict, then this type conflict must be logged in a Vec somewhere

*/

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PotentialType {
    // TODO: Poly cannot use String, must resolve to declaration of polymorphic type such as 'a
    Poly(Reasons, String, Vec<Rc<InterfaceDecl>>), // type name, then list of Interfaces it must match
    Unit(Reasons),
    Int(Reasons),
    Float(Reasons),
    Bool(Reasons),
    String(Reasons),
    Function(Reasons, Vec<TypeVar>, TypeVar),
    Tuple(Reasons, Vec<TypeVar>),
    Nominal(Reasons, Nominal, Vec<TypeVar>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SolvedType {
    // TODO: Poly cannot use String, must resolve to declaration of polymorphic type such as 'a
    Poly(String, Vec<Rc<InterfaceDecl>>), // type name, then list of Interfaces it must match
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<SolvedType>, Box<SolvedType>),
    Tuple(Vec<SolvedType>),
    Nominal(Nominal, Vec<SolvedType>),
}

// TODO: Might need to make a public and a non-public version of this.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Nominal {
    Struct(Rc<StructDef>),
    Enum(Rc<EnumDef>),
    ForeignType(Identifier),
    Array,
}

impl Nominal {
    pub(crate) fn name(&self) -> &str {
        match self {
            Self::Struct(struct_def) => &struct_def.name.v,
            Self::Enum(enum_def) => &enum_def.name.v,
            Self::ForeignType(name) => &name.v,
            Self::Array => "array",
        }
    }
}

impl SolvedType {
    pub(crate) fn monotype(&self) -> Option<Monotype> {
        match self {
            Self::Poly(..) => None,
            Self::Unit => Some(Monotype::Unit),
            Self::Int => Some(Monotype::Int),
            Self::Float => Some(Monotype::Float),
            Self::Bool => Some(Monotype::Bool),
            Self::String => Some(Monotype::String),
            Self::Function(args, out) => {
                let mut args2: Vec<Monotype> = vec![];
                for arg in args {
                    if let Some(arg) = arg.monotype() {
                        args2.push(arg);
                    } else {
                        return None;
                    }
                }
                let out = out.monotype()?;
                Some(Monotype::Function(args2, out.into()))
            }
            Self::Tuple(elems) => {
                let mut elems2 = vec![];
                for elem in elems {
                    if let Some(elem) = elem.monotype() {
                        elems2.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(Monotype::Tuple(elems2))
            }
            Self::Nominal(ident, params) => {
                let mut params2: Vec<Monotype> = vec![];
                for param in params {
                    if let Some(param) = param.monotype() {
                        params2.push(param);
                    } else {
                        return None;
                    }
                }
                Some(Monotype::Nominal(ident.clone(), params2))
            }
        }
    }

    pub(crate) fn is_overloaded(&self) -> bool {
        match self {
            Self::Poly(_, interfaces) => !interfaces.is_empty(),
            Self::Unit => false,
            Self::Int => false,
            Self::Float => false,
            Self::Bool => false,
            Self::String => false,
            Self::Function(args, out) => {
                args.iter().any(|ty| ty.is_overloaded()) || out.is_overloaded()
            }
            Self::Tuple(tys) => tys.iter().any(|ty| ty.is_overloaded()),
            Self::Nominal(_, tys) => tys.iter().any(|ty| ty.is_overloaded()),
        }
    }
}

// This is the fully instantiated AKA monomorphized type of an interface's implementation
// subset of SolvedType. SolvedType without poly
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Monotype {
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<Monotype>, Box<Monotype>),
    Tuple(Vec<Monotype>),
    Nominal(Nominal, Vec<Monotype>),
}

// If two types don't share the same key, they must be in conflict
// (If two types share the same key, they may or may not be in conflict)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TypeKey {
    Poly,
    TyApp(Nominal, u8), // u8 represents the number of type params
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(u8), // u8 represents the number of arguments
    Tuple(u8),    // u8 represents the number of elements
}

// TODO: Split Prov into two types
// 1. TypeIdentity
// 2. ConstraintProvenance/ErrorProvenance or something

// Provenances are used to:
// (1) give the *unique* identity of a skolem (type to be solved) (UnifVar) in the SolutionMap
// (2) track the origins (plural!) of a type's constraints for error reporting
// TODO: Does Prov really need to be that deeply nested? Will there really be FuncArg -> InstantiatedPoly -> BinopLeft -> Node? Or can we simplify here?
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Prov {
    Node(NodeId), // the type of an expression or statement located at NodeId
    InstantiateUdtParam(Box<Prov>, u8),
    InstantiatePoly(Box<Prov>, String),
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
    ListElem(Box<Prov>),
    StructField(String, NodeId),
    IndexAccess,
    VariantNoData(Box<Prov>), // the type of the data of a variant with no data, always Unit.
}

impl Prov {
    // TODO: Can we make this not Optional? Only reason it would fail is if the last prov in the chain is a builtin
    // TODO: remove Builtin prov for this reason, defeats the purpose. Builtins should be declared in the PRELUDE, and that declaration will be the Prov.
    fn get_location(&self) -> Option<NodeId> {
        match self {
            Prov::Node(id) => Some(*id),
            Prov::InstantiateUdtParam(inner, _)
            | Prov::InstantiatePoly(inner, _)
            | Prov::FuncArg(inner, _)
            | Prov::FuncOut(inner)
            | Prov::ListElem(inner)
            | Prov::VariantNoData(inner) => inner.get_location(),
            Prov::StructField(_, _) => None,
            Prov::IndexAccess => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Reason {
    // TODO: NodeId is too vague. Remove
    Node(NodeId),     // the type of an expression or statement located at NodeId
    Builtin(Builtin), // a builtin function or constant, which doesn't exist in the AST
    Effect(u16),

    UdtDef(Box<Reason>), // TODO: replace this with 'Declaration'
    BinopLeft(Box<Reason>),
    BinopRight(Box<Reason>),
    ListElem(Box<Reason>),
    StructField(String, NodeId),
    IndexAccess,
    VariantNoData(Box<Reason>), // the type of the data of a variant with no data, always Unit.
}

impl PotentialType {
    fn key(&self) -> TypeKey {
        match self {
            PotentialType::Poly(_, _, _) => TypeKey::Poly,
            PotentialType::Unit(_) => TypeKey::Unit,
            PotentialType::Int(_) => TypeKey::Int,
            PotentialType::Float(_) => TypeKey::Float,
            PotentialType::Bool(_) => TypeKey::Bool,
            PotentialType::String(_) => TypeKey::String,
            PotentialType::Function(_, args, _) => TypeKey::Function(args.len() as u8),
            PotentialType::Tuple(_, elems) => TypeKey::Tuple(elems.len() as u8),
            PotentialType::Nominal(_, ident, params) => {
                TypeKey::TyApp(ident.clone(), params.len() as u8)
            }
        }
    }

    fn solution(&self) -> Option<SolvedType> {
        match self {
            Self::Bool(_) => Some(SolvedType::Bool),
            Self::Int(_) => Some(SolvedType::Int),
            Self::Float(_) => Some(SolvedType::Float),
            Self::String(_) => Some(SolvedType::String),
            Self::Unit(_) => Some(SolvedType::Unit),
            Self::Poly(_, ident, interfaces) => {
                Some(SolvedType::Poly(ident.clone(), interfaces.clone()))
            }
            Self::Function(_, args, out) => {
                let mut args2: Vec<SolvedType> = vec![];
                for arg in args {
                    if let Some(arg) = arg.solution() {
                        args2.push(arg);
                    } else {
                        return None;
                    }
                }
                let out = out.solution()?;
                Some(SolvedType::Function(args2, out.into()))
            }
            Self::Tuple(_, elems) => {
                let mut elems2: Vec<SolvedType> = vec![];
                for elem in elems {
                    if let Some(elem) = elem.solution() {
                        elems2.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(SolvedType::Tuple(elems2))
            }
            Self::Nominal(_, ident, params) => {
                let mut params2: Vec<SolvedType> = vec![];
                for param in params {
                    if let Some(param) = param.solution() {
                        params2.push(param);
                    } else {
                        return None;
                    }
                }
                Some(SolvedType::Nominal(ident.clone(), params2))
            }
        }
    }

    pub(crate) fn reasons(&self) -> &Reasons {
        match self {
            Self::Poly(provs, _, _)
            | Self::Unit(provs)
            | Self::Int(provs)
            | Self::Float(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _)
            | Self::Nominal(provs, _, _) => provs,
        }
    }

    fn make_unit(reason: Reason) -> PotentialType {
        PotentialType::Unit(reasons_singleton(reason))
    }

    fn make_int(reason: Reason) -> PotentialType {
        PotentialType::Int(reasons_singleton(reason))
    }

    fn make_float(reason: Reason) -> PotentialType {
        PotentialType::Float(reasons_singleton(reason))
    }

    fn make_bool(reason: Reason) -> PotentialType {
        PotentialType::Bool(reasons_singleton(reason))
    }

    fn make_string(reason: Reason) -> PotentialType {
        PotentialType::String(reasons_singleton(reason))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, reason: Reason) -> PotentialType {
        PotentialType::Function(reasons_singleton(reason), args, out)
    }

    fn make_tuple(elems: Vec<TypeVar>, reason: Reason) -> PotentialType {
        PotentialType::Tuple(reasons_singleton(reason), elems)
    }

    fn make_poly(
        reason: Reason,
        ident: String,
        interfaces: Vec<Rc<InterfaceDecl>>,
    ) -> PotentialType {
        PotentialType::Poly(reasons_singleton(reason), ident, interfaces)
    }

    fn make_nominal(reason: Reason, nominal: Nominal, params: Vec<TypeVar>) -> PotentialType {
        PotentialType::Nominal(reasons_singleton(reason), nominal, params)
    }
}

impl TypeVar {
    // TODO: does clone_data() really need to be used everywhere? Or can you use with_data(F) in a lot of places?
    pub(crate) fn solution(&self) -> Option<SolvedType> {
        self.0.clone_data().solution()
    }

    fn solved(&self) -> bool {
        self.0.with_data(|d| d.locked)
    }

    // TODO: arguments are named 'expected' and 'actual'. Does order actuall matter or not? Should it?
    fn merge(mut expected: TypeVar, mut actual: TypeVar) {
        expected
            .0
            .union_with(&mut actual.0, TypeVarData::merge_data);
    }

    fn single(&self) -> Option<PotentialType> {
        let types = self.0.clone_data().types;
        if types.len() == 1 {
            Some(types.values().next().unwrap().clone())
        } else {
            None
        }
    }

    // Creates a clone of a Type with polymorphic variables not in scope replaced with fresh unifvars
    fn instantiate(
        self,
        polyvar_scope: PolyvarScope,
        ctx: &mut StaticsContext,
        prov: Prov,
    ) -> TypeVar {
        let data = self.0.clone_data();
        if data.types.len() != 1 {
            return self;
        }
        let ty = data.types.into_values().next().unwrap();
        let ty = match ty {
            PotentialType::Unit(_)
            | PotentialType::Int(_)
            | PotentialType::Float(_)
            | PotentialType::Bool(_)
            | PotentialType::String(_) => {
                ty // noop
            }
            PotentialType::Poly(_, ref ident, ref interfaces) => {
                if !polyvar_scope.lookup_poly(ident) {
                    let ret = TypeVar::fresh(
                        ctx,
                        Prov::InstantiatePoly(Box::new(prov.clone()), ident.clone()),
                    );
                    // TODO: Don't remove below. Need to add interface constraint check back later
                    // let mut extension = Vec::new();
                    // for i in interfaces {
                    //     extension.push((i.clone(), prov.clone()));
                    // }
                    // ctx.types_constrained_to_interfaces
                    //     .entry(ret.clone())
                    //     .or_default()
                    //     .extend(extension);
                    return ret; // instantiation occurs here
                } else {
                    ty // noop
                }
            }
            PotentialType::Nominal(provs, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, prov.clone()))
                    .collect();
                PotentialType::Nominal(provs, ident, params)
            }
            PotentialType::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, prov.clone()))
                    .collect();
                let out = out.instantiate(polyvar_scope.clone(), ctx, prov.clone());
                PotentialType::Function(provs, args, out)
            }
            PotentialType::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, prov.clone()))
                    .collect();
                PotentialType::Tuple(provs, elems)
            }
        };
        let mut types = BTreeMap::new();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData {
            types,
            locked: data.locked,
        };
        let tvar = TypeVar(UnionFindNode::new(data_instantiated));
        ctx.unifvars.insert(prov, tvar.clone());
        tvar
    }

    // Creates a *new* Type with polymorphic variabels replaced by subtitutions
    pub(crate) fn subst(
        self,
        polyvar_scope: PolyvarScope,
        prov: Prov,
        substitution: &BTreeMap<String, TypeVar>,
    ) -> TypeVar {
        let data = self.0.clone_data();
        if data.types.len() == 1 {
            let ty = data.types.into_values().next().unwrap();

            let ty = match ty {
                PotentialType::Unit(_)
                | PotentialType::Int(_)
                | PotentialType::Float(_)
                | PotentialType::Bool(_)
                | PotentialType::String(_) => {
                    ty // noop
                }
                PotentialType::Poly(_, ref ident, ref _interfaces) => {
                    if let Some(ty) = substitution.get(ident) {
                        return ty.clone(); // substitution occurs here
                    } else {
                        ty // noop
                    }
                }
                PotentialType::Nominal(provs, ident, params) => {
                    let params = params
                        .into_iter()
                        .map(|ty| ty.subst(polyvar_scope.clone(), prov.clone(), substitution))
                        .collect();
                    PotentialType::Nominal(provs, ident, params)
                }
                PotentialType::Function(provs, args, out) => {
                    let args = args
                        .into_iter()
                        .map(|ty| ty.subst(polyvar_scope.clone(), prov.clone(), substitution))
                        .collect();
                    let out = out.subst(polyvar_scope.clone(), prov, substitution);
                    PotentialType::Function(provs, args, out)
                }
                PotentialType::Tuple(provs, elems) => {
                    let elems = elems
                        .into_iter()
                        .map(|ty| ty.subst(polyvar_scope.clone(), prov.clone(), substitution))
                        .collect();
                    PotentialType::Tuple(provs, elems)
                }
            };
            let mut types = BTreeMap::new();
            types.insert(ty.key(), ty);
            let new_data = TypeVarData {
                types,
                locked: data.locked,
            };
            TypeVar(UnionFindNode::new(new_data))
        } else {
            self // noop
        }
    }

    pub(crate) fn from_node(ctx: &mut StaticsContext, id: NodeId) -> TypeVar {
        let prov = Prov::Node(id);
        Self::fresh(ctx, prov)
    }

    pub(crate) fn fresh(ctx: &mut StaticsContext, prov: Prov) -> TypeVar {
        match ctx.unifvars.get(&prov) {
            Some(ty) => ty.clone(),
            None => {
                let ty = TypeVar(UnionFindNode::new(TypeVarData::new()));
                ctx.unifvars.insert(prov, ty.clone());
                ty
            }
        }
    }

    fn singleton_solved(potential_type: PotentialType) -> TypeVar {
        TypeVar(UnionFindNode::new(TypeVarData::singleton_solved(
            potential_type,
        )))
    }

    pub(crate) fn make_unit(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_unit(reason))
    }

    fn make_int(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_int(reason))
    }

    fn make_float(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_float(reason))
    }

    fn make_bool(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_bool(reason))
    }

    fn make_string(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_string(reason))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_func(args, out, reason))
    }

    fn make_tuple(elems: Vec<TypeVar>, reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_tuple(elems, reason))
    }

    fn make_poly(reason: Reason, ident: String, interfaces: Vec<Rc<InterfaceDecl>>) -> TypeVar {
        Self::singleton_solved(PotentialType::make_poly(reason, ident, interfaces))
    }

    fn make_nominal(reason: Reason, nominal: Nominal, params: Vec<TypeVar>) -> TypeVar {
        Self::singleton_solved(PotentialType::make_nominal(reason, nominal, params))
    }

    // return true if the type is a nominal type with at least one parameter instantiated
    // this is used to see if an implementation of an interface is for an instantiated nominal, which is not allowed
    // example: implement ToString for list<int> rather than list<'a>
    pub(crate) fn is_instantiated_nominal(&self) -> bool {
        let Some(ty) = self.single() else {
            return false;
        };
        match ty {
            // return true if an enumt with at least one parameter instantiated
            PotentialType::Nominal(_, _, tys) => !tys
                .iter()
                .all(|ty| matches!(ty.single(), Some(PotentialType::Poly(..)))),
            _ => false,
        }
    }

    fn underdetermined(&self) -> bool {
        self.0.with_data(|data| data.types.is_empty())
    }
}

// TODO: What exactly does 'tyvar_of_declaration' actually mean?
// TODO: In a lot of these cases, we shouldn't really give a TypeVar, because the type is fully known.
// TODO: a lot of code duplication with ast_type_to_statics_type/solved_type
fn tyvar_of_declaration(
    ctx: &mut StaticsContext,
    decl: &Declaration,
    id: NodeId,
    polyvar_scope: PolyvarScope,
) -> Option<TypeVar> {
    match decl {
        Declaration::FreeFunction(f, _) => Some(TypeVar::from_node(ctx, f.name.id)),
        Declaration::ForeignFunction { decl, .. } => Some(TypeVar::from_node(ctx, decl.name.id)),
        Declaration::InterfaceDef(..) => None,
        Declaration::InterfaceMethod {
            iface_def,
            method,
            fully_qualified_name: _,
        } => Some(TypeVar::from_node(
            ctx,
            iface_def.methods[*method as usize].id(),
        )),
        Declaration::Enum(enum_def) => {
            let nparams = enum_def.ty_args.len();
            let mut params = vec![];
            let mut substitution = BTreeMap::new();
            for i in 0..nparams {
                params.push(TypeVar::fresh(
                    ctx,
                    Prov::InstantiateUdtParam(Box::new(Prov::Node(id)), i as u8),
                ));
                // TODO: don't do this silly downcast.
                // ty_args should just be a Vec<Identifier> most likely
                let TypeKind::Poly(ty_arg, _) = &*enum_def.ty_args[i].kind else {
                    panic!()
                };
                substitution.insert(ty_arg.v.clone(), params[i].clone());
            }
            Some(TypeVar::make_nominal(
                Reason::UdtDef(Box::new(Reason::Node(id))), // TODO: change to Reason::Declaration
                Nominal::Enum(enum_def.clone()),
                params,
            ))
        }
        Declaration::EnumVariant { enum_def, variant } => {
            let nparams = enum_def.ty_args.len();
            let mut params = vec![];
            let mut substitution = BTreeMap::new();
            for i in 0..nparams {
                params.push(TypeVar::fresh(
                    ctx,
                    Prov::InstantiateUdtParam(Box::new(Prov::Node(id)), i as u8),
                ));
                // TODO: don't do this silly downcast.
                // ty_args should just be a Vec<Identifier> most likely
                let TypeKind::Poly(ty_arg, _) = &*enum_def.ty_args[i].kind else {
                    panic!()
                };
                substitution.insert(ty_arg.v.clone(), params[i].clone());
            }
            let def_type = TypeVar::make_nominal(
                Reason::UdtDef(Box::new(Reason::Node(id))),
                Nominal::Enum(enum_def.clone()),
                params,
            );

            let the_variant = &enum_def.variants[*variant as usize];
            match &the_variant.data {
                None => Some(def_type),
                Some(ty) => match &*ty.kind {
                    TypeKind::Unit => Some(def_type),
                    TypeKind::Tuple(elems) => {
                        let args = elems
                            .iter()
                            .map(|e| {
                                let e = ast_type_to_typevar(ctx, e.clone());
                                e.clone().subst(
                                    polyvar_scope.clone(),
                                    Prov::Node(id),
                                    &substitution,
                                )
                            })
                            .collect();
                        Some(TypeVar::make_func(args, def_type, Reason::Node(id)))
                    }
                    _ => {
                        let ty = ast_type_to_typevar(ctx, ty.clone());
                        Some(TypeVar::make_func(
                            vec![ty
                                .clone()
                                .subst(polyvar_scope, Prov::Node(id), &substitution)],
                            def_type,
                            Reason::Node(id),
                        ))
                    }
                },
            }
        }
        Declaration::Struct(struct_def) => {
            let nparams = struct_def.ty_args.len();
            let mut params = vec![];
            let mut substitution = BTreeMap::new();
            for i in 0..nparams {
                params.push(TypeVar::fresh(
                    ctx,
                    Prov::InstantiateUdtParam(Box::new(Prov::Node(id)), i as u8),
                ));
                // TODO: don't do this silly downcast.
                // ty_args should just be a Vec<Identifier> most likely
                let TypeKind::Poly(ty_arg, _) = &*struct_def.ty_args[i].kind else {
                    panic!()
                };
                substitution.insert(ty_arg.v.clone(), params[i].clone());
            }
            let def_type = TypeVar::make_nominal(
                Reason::UdtDef(Box::new(Reason::Node(id))),
                Nominal::Struct(struct_def.clone()),
                params,
            );
            let fields = struct_def
                .fields
                .iter()
                .map(|f| {
                    let ty = ast_type_to_typevar(ctx, f.ty.clone());
                    ty.clone()
                        .subst(polyvar_scope.clone(), Prov::Node(id), &substitution)
                })
                .collect();
            Some(TypeVar::make_func(fields, def_type, Reason::Node(id)))
        }
        Declaration::ForeignType(ident) => Some(TypeVar::make_nominal(
            Reason::UdtDef(Box::new(Reason::Node(id))),
            Nominal::ForeignType(ident.clone()),
            vec![],
        )),
        Declaration::Array => {
            let mut params = vec![];
            let mut substitution = BTreeMap::new();
            params.push(TypeVar::fresh(
                ctx,
                Prov::InstantiateUdtParam(Box::new(Prov::Node(id)), 0),
            ));

            substitution.insert("a", params[0].clone());

            let def_type = TypeVar::make_nominal(
                Reason::UdtDef(Box::new(Reason::Node(id))),
                Nominal::Array,
                params,
            );

            Some(TypeVar::make_func(vec![], def_type, Reason::Node(id)))
        }
        Declaration::Polytype(_) => {
            panic!() // TODO: handle? don't handle?
        }
        Declaration::Builtin(builtin) => {
            let ty_signature = builtin.type_signature();
            Some(solved_type_to_typevar(
                ty_signature,
                Reason::Builtin(*builtin),
            ))
        }
        Declaration::Effect(e) => {
            let effect = &ctx.effects[*e as usize];
            let ty_signature = &effect.type_signature;
            let func_type =
                Monotype::Function(ty_signature.0.clone(), ty_signature.1.clone().into());
            Some(monotype_to_typevar(func_type, Reason::Effect(*e)))
        }
        Declaration::Var(node_id) => Some(TypeVar::from_node(ctx, *node_id)),
    }
}

fn types_of_binop(
    ctx: &mut StaticsContext,
    opcode: &BinaryOperator,
    id: NodeId,
) -> (TypeVar, TypeVar, TypeVar) {
    let num_iface_decl = ctx
        .global_namespace
        .namespaces
        .get("prelude")
        .and_then(|p| p.declarations.get("Num"))
        .unwrap();
    let Declaration::InterfaceDef(num_iface_def) = num_iface_decl else {
        panic!()
    };

    let equal_iface_decl = ctx
        .global_namespace
        .namespaces
        .get("prelude")
        .and_then(|p| p.declarations.get("Equal"))
        .unwrap();
    let Declaration::InterfaceDef(equal_iface_def) = equal_iface_decl else {
        panic!()
    };

    let tostring_iface_decl = ctx
        .global_namespace
        .namespaces
        .get("prelude")
        .and_then(|p| p.declarations.get("ToString"))
        .unwrap();
    let Declaration::InterfaceDef(tostring_iface_def) = tostring_iface_decl else {
        panic!()
    };

    let prov_left = Reason::BinopLeft(Reason::Node(id).into());
    let prov_right = Reason::BinopRight(Reason::Node(id).into());
    let prov_out = Reason::Node(id);
    match opcode {
        BinaryOperator::And | BinaryOperator::Or => (
            TypeVar::make_bool(prov_left),
            TypeVar::make_bool(prov_right),
            TypeVar::make_bool(prov_out),
        ),
        BinaryOperator::Add
        | BinaryOperator::Subtract
        | BinaryOperator::Multiply
        | BinaryOperator::Divide
        | BinaryOperator::Pow => {
            let ty_left =
                TypeVar::make_poly(prov_left, "a".to_owned(), vec![num_iface_def.clone()]);
            let ty_right =
                TypeVar::make_poly(prov_right, "a".to_owned(), vec![num_iface_def.clone()]);
            let ty_out = TypeVar::make_poly(prov_out, "a".to_owned(), vec![num_iface_def.clone()]);
            constrain(ctx, ty_left.clone(), ty_right.clone());
            constrain(ctx, ty_left.clone(), ty_out.clone());
            (ty_left, ty_right, ty_out)
        }
        BinaryOperator::Mod => (
            TypeVar::make_int(prov_left),
            TypeVar::make_int(prov_right),
            TypeVar::make_int(prov_out),
        ),
        BinaryOperator::LessThan
        | BinaryOperator::GreaterThan
        | BinaryOperator::LessThanOrEqual
        | BinaryOperator::GreaterThanOrEqual => {
            let ty_left =
                TypeVar::make_poly(prov_left, "a".to_owned(), vec![num_iface_def.clone()]);
            let ty_right =
                TypeVar::make_poly(prov_right, "a".to_owned(), vec![num_iface_def.clone()]);
            constrain(ctx, ty_left.clone(), ty_right.clone());
            let ty_out = TypeVar::make_bool(prov_out);
            (ty_left, ty_right, ty_out)
        }
        BinaryOperator::Format => {
            let ty_left =
                TypeVar::make_poly(prov_left, "a".to_owned(), vec![tostring_iface_def.clone()]);
            let ty_right =
                TypeVar::make_poly(prov_right, "b".to_owned(), vec![tostring_iface_def.clone()]);
            let ty_out = TypeVar::make_string(prov_out);
            (ty_left, ty_right, ty_out)
        }
        BinaryOperator::Equal => {
            let ty_left =
                TypeVar::make_poly(prov_left, "a".to_owned(), vec![equal_iface_def.clone()]);
            let ty_right =
                TypeVar::make_poly(prov_right, "a".to_owned(), vec![equal_iface_def.clone()]);
            constrain(ctx, ty_left.clone(), ty_right.clone());
            (ty_left, ty_right, TypeVar::make_bool(prov_out))
        }
    }
}

pub(crate) fn ast_type_to_solved_type(
    ctx: &StaticsContext,
    ast_type: Rc<AstType>,
) -> Option<SolvedType> {
    match &*ast_type.kind {
        TypeKind::Poly(ident, iface_names) => {
            let mut ifaces = vec![];
            for iface_name in iface_names {
                let lookup = ctx.resolution_map.get(&iface_name.id);
                if let Some(Declaration::InterfaceDef(iface_def)) = lookup {
                    ifaces.push(iface_def.clone());
                }
            }
            Some(SolvedType::Poly(ident.v.clone(), ifaces))
        }
        TypeKind::Identifier(_) => {
            let lookup = ctx.resolution_map.get(&ast_type.id)?;
            match lookup {
                Declaration::Array => Some(SolvedType::Nominal(Nominal::Array, vec![])),
                Declaration::Struct(struct_def) => Some(SolvedType::Nominal(
                    Nominal::Struct(struct_def.clone()),
                    vec![],
                )),
                Declaration::Enum(enum_def) => {
                    Some(SolvedType::Nominal(Nominal::Enum(enum_def.clone()), vec![]))
                }
                Declaration::ForeignType(ident) => Some(SolvedType::Nominal(
                    Nominal::ForeignType(ident.clone()),
                    vec![],
                )),
                Declaration::FreeFunction(_, _)
                | Declaration::ForeignFunction { .. }
                | Declaration::InterfaceDef(_)
                | Declaration::InterfaceMethod { .. }
                | Declaration::EnumVariant { .. }
                | Declaration::Polytype(_)
                | Declaration::Builtin(_)
                | Declaration::Effect(_)
                | Declaration::Var(_) => None,
            }
        }
        TypeKind::Ap(identifier, args) => {
            let mut sargs = vec![];
            for arg in args {
                sargs.push(ast_type_to_solved_type(ctx, arg.clone())?);
            }
            let lookup = ctx.resolution_map.get(&identifier.id)?;
            match lookup {
                Declaration::Array => Some(SolvedType::Nominal(Nominal::Array, sargs)),
                Declaration::Struct(struct_def) => Some(SolvedType::Nominal(
                    Nominal::Struct(struct_def.clone()),
                    vec![],
                )),
                Declaration::Enum(enum_def) => {
                    Some(SolvedType::Nominal(Nominal::Enum(enum_def.clone()), sargs))
                }
                Declaration::ForeignType(ident) => Some(SolvedType::Nominal(
                    Nominal::ForeignType(ident.clone()),
                    vec![],
                )),
                Declaration::FreeFunction(_, _)
                | Declaration::ForeignFunction { .. }
                | Declaration::InterfaceDef(_)
                | Declaration::InterfaceMethod { .. }
                | Declaration::EnumVariant { .. }
                | Declaration::Polytype(_)
                | Declaration::Builtin(_)
                | Declaration::Effect(_)
                | Declaration::Var(_) => None,
            }
        }
        TypeKind::Unit => Some(SolvedType::Unit),
        TypeKind::Int => Some(SolvedType::Int),
        TypeKind::Float => Some(SolvedType::Float),
        TypeKind::Bool => Some(SolvedType::Bool),
        TypeKind::Str => Some(SolvedType::String),
        TypeKind::Function(args, ret) => {
            let mut sargs = vec![];
            for arg in args {
                let sarg = ast_type_to_solved_type(ctx, arg.clone())?;
                sargs.push(sarg);
            }
            let sret = ast_type_to_solved_type(ctx, ret.clone())?;
            Some(SolvedType::Function(sargs, sret.into()))
        }
        TypeKind::Tuple(elems) => {
            let mut selems = vec![];
            for elem in elems {
                let selem = ast_type_to_solved_type(ctx, elem.clone())?;
                selems.push(selem);
            }
            Some(SolvedType::Tuple(selems))
        }
    }
}

pub(crate) fn ast_type_to_typevar(ctx: &mut StaticsContext, ast_type: Rc<AstType>) -> TypeVar {
    match &*ast_type.kind {
        TypeKind::Poly(ident, iface_names) => {
            let mut interfaces = vec![];
            for iface_name in iface_names {
                let lookup = ctx.resolution_map.get(&iface_name.id);
                if let Some(Declaration::InterfaceDef(iface_def)) = lookup {
                    interfaces.push(iface_def.clone());
                }
            }
            TypeVar::make_poly(Reason::Node(ast_type.id()), ident.v.clone(), interfaces)
        }
        TypeKind::Identifier(ident) => {
            let lookup = ctx.resolution_map.get(&ast_type.id);
            match lookup {
                Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                    Reason::Node(ast_type.id()),
                    Nominal::Enum(enum_def.clone()),
                    vec![],
                ),
                Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                    Reason::Node(ast_type.id()),
                    Nominal::Struct(struct_def.clone()),
                    vec![],
                ),
                Some(Declaration::Array) => {
                    TypeVar::make_nominal(Reason::Node(ast_type.id()), Nominal::Array, vec![])
                }
                Some(Declaration::ForeignType(ident)) => TypeVar::make_nominal(
                    Reason::Node(ast_type.id()),
                    Nominal::ForeignType(ident.clone()),
                    vec![],
                ),
                _ => {
                    panic!("could not resolve {}", ident) // TODO: remove panic
                }
            }
        }
        TypeKind::Ap(ident, params) => {
            let lookup = ctx.resolution_map.get(&ident.id);
            match lookup {
                Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                    Reason::Node(ast_type.id()),
                    Nominal::Enum(enum_def.clone()),
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                    Reason::Node(ast_type.id()),
                    Nominal::Struct(struct_def.clone()),
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                Some(Declaration::Array) => TypeVar::make_nominal(
                    Reason::Node(ast_type.id()),
                    Nominal::Array,
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                _ => {
                    panic!("could not resolve {}", ident.v) // TODO: remove panic
                }
            }
        }
        TypeKind::Unit => TypeVar::make_unit(Reason::Node(ast_type.id())),
        TypeKind::Int => TypeVar::make_int(Reason::Node(ast_type.id())),
        TypeKind::Float => TypeVar::make_float(Reason::Node(ast_type.id())),
        TypeKind::Bool => TypeVar::make_bool(Reason::Node(ast_type.id())),
        TypeKind::Str => TypeVar::make_string(Reason::Node(ast_type.id())),
        TypeKind::Function(lhs, rhs) => TypeVar::make_func(
            lhs.iter()
                .map(|t| ast_type_to_typevar(ctx, t.clone()))
                .collect(),
            ast_type_to_typevar(ctx, rhs.clone()),
            Reason::Node(ast_type.id()),
        ),
        TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_typevar(ctx, t.clone()));
            }
            TypeVar::make_tuple(statics_types, Reason::Node(ast_type.id()))
        }
    }
}

pub(crate) type Reasons = RefCell<BTreeSet<Reason>>;

fn reasons_singleton(reason: Reason) -> Reasons {
    let mut set = BTreeSet::new();
    set.insert(reason);
    RefCell::new(set)
}

#[derive(Debug, Clone)]
pub(crate) enum Mode {
    Syn,
    Ana { expected: TypeVar },
}

// TODO: arguments are named 'expected' and 'actual'. Does order actuall matter or not? Should it?
pub(crate) fn constrain(ctx: &mut StaticsContext, expected: TypeVar, actual: TypeVar) {
    match (expected.solved(), actual.solved()) {
        // Since both TypeVars are already solved, an error is logged if their data do not match
        (true, true) => {
            constrain_solved_typevars(ctx, expected, actual);
        }
        // Since exactly one of the TypeVars is unsolved, its data will be updated with information from the solved TypeVar
        (false, true) => {
            let potential_ty = actual.0.clone_data().types.into_iter().next().unwrap().1;
            expected.0.with_data(|d| {
                if d.types.is_empty() {
                    d.locked = true
                }
                d.extend(potential_ty)
            });
        }
        (true, false) => {
            let potential_ty = expected.0.clone_data().types.into_iter().next().unwrap().1;
            actual.0.with_data(|d| {
                if d.types.is_empty() {
                    d.locked = true
                }
                d.extend(potential_ty)
            });
        }
        // Since both TypeVars are unsolved, they are unioned and their data is merged
        (false, false) => {
            TypeVar::merge(expected, actual);
        }
    }
}

fn constrain_solved_typevars(ctx: &mut StaticsContext, expected: TypeVar, actual: TypeVar) {
    let (key1, ty1) = expected.0.clone_data().types.into_iter().next().unwrap();
    let (key2, ty2) = actual.0.clone_data().types.into_iter().next().unwrap();
    if key1 != key2 {
        ctx.errors.push(Error::ConflictingTypes { ty1, ty2 })
    } else {
        TypeVar::merge(expected, actual);
    }
}

// TODO: Can this be done in resolve() instead?
#[derive(Clone)]
pub(crate) struct PolyvarScope {
    // keep track of polymorphic type variables currently in scope (such as 'a)
    // TODO: cannot use String, must resolve to declaration of polymorphic type
    // Just because two types are named 'a doesn't mean they're the same 'a
    // TODO LAST HERE
    polyvars_in_scope: Environment<String, ()>,
}
impl PolyvarScope {
    pub(crate) fn empty() -> Self {
        Self {
            polyvars_in_scope: Environment::empty(),
        }
    }

    fn add_polys(&self, ty: &TypeVar) {
        let Some(ty) = ty.single() else {
            return;
        };
        match ty {
            PotentialType::Poly(_, ident, _interfaces) => {
                self.polyvars_in_scope.extend(ident.clone(), ());
            }
            PotentialType::Nominal(_, _, params) => {
                for param in params {
                    self.add_polys(&param);
                }
            }
            PotentialType::Function(_, args, out) => {
                for arg in args {
                    self.add_polys(&arg);
                }
                self.add_polys(&out);
            }
            PotentialType::Tuple(_, elems) => {
                for elem in elems {
                    self.add_polys(&elem);
                }
            }
            _ => {}
        }
    }

    fn lookup_poly(&self, id: &String) -> bool {
        self.polyvars_in_scope.lookup(id).is_some()
    }

    fn new_scope(&self) -> Self {
        Self {
            polyvars_in_scope: self.polyvars_in_scope.new_scope(),
        }
    }
}

// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub(crate) fn result_of_constraint_solving(ctx: &mut StaticsContext) {
    // get list of type conflicts
    let mut type_conflicts = Vec::new();
    for (prov, tyvar) in ctx.unifvars.iter() {
        let type_suggestions = tyvar.0.clone_data().types; // TODO why not just check if it's solved?
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions.clone());

            ctx.errors.push(Error::ConflictingUnifvar {
                types: type_suggestions,
            });
        } else if type_suggestions.is_empty() {
            if let Prov::Node(id) = prov {
                ctx.errors
                    .push(Error::UnconstrainedUnifvar { node_id: *id });
            }
        }
    }
}

pub(crate) fn generate_constraints_file(file: Rc<FileAst>, ctx: &mut StaticsContext) {
    for items in file.items.iter() {
        generate_constraints_item(Mode::Syn, items.clone(), ctx);
    }
}

fn generate_constraints_item(mode: Mode, stmt: Rc<Item>, ctx: &mut StaticsContext) {
    match &*stmt.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(stmt) => {
            generate_constraints_stmt(PolyvarScope::empty(), mode, stmt.clone(), ctx)
        }
        ItemKind::InterfaceImpl(iface_impl) => {
            let impl_ty = ast_type_to_typevar(ctx, iface_impl.typ.clone());

            let lookup = ctx.resolution_map.get(&iface_impl.iface.id).cloned();
            if let Some(Declaration::InterfaceDef(iface_decl)) = lookup {
                // TODO: This logic is performed for the interface definition every time an implementation is found
                // Do the logic only once, memoize the result.
                // TODO: Shouldn't use type inference to infer the types of the properties/methods. They are already annotated. They are already solved.
                for method in &iface_decl.methods {
                    let ty_annot = ast_type_to_typevar(ctx, method.ty.clone());
                    let node_ty = TypeVar::from_node(ctx, method.id());
                    constrain(ctx, node_ty.clone(), ty_annot.clone());
                }
                for f in &iface_impl.methods {
                    let method_name = f.name.v.clone();
                    if let Some(interface_method) =
                        iface_decl.methods.iter().find(|m| m.name.v == method_name)
                    {
                        let mut substitution = BTreeMap::new();
                        substitution.insert("a".to_string(), impl_ty.clone());

                        let interface_method_ty =
                            ast_type_to_typevar(ctx, interface_method.ty.clone());
                        let actual = TypeVar::from_node(ctx, interface_method.id());
                        constrain(ctx, interface_method_ty.clone(), actual);

                        let expected = interface_method_ty.clone().subst(
                            PolyvarScope::empty(),
                            Prov::Node(stmt.id),
                            &substitution,
                        );

                        let actual = TypeVar::from_node(ctx, f.name.id);
                        constrain(ctx, expected, actual);

                        generate_constraints_fn_def(ctx, PolyvarScope::empty(), f, f.name.id);
                    }
                }

                let impl_list = ctx.interface_impls.entry(iface_decl.clone()).or_default();

                impl_list.push(iface_impl.clone());
            }
        }
        ItemKind::TypeDef(typdefkind) => match &**typdefkind {
            // TypeDefKind::Alias(ident, ty) => {
            //     let left = TypeVar::fresh(ctx, Prov::Alias(ident.clone()));
            //     let right = ast_type_to_statics_type(ctx, ty.clone());
            //     constrain(ctx,left, right);
            // }
            TypeDefKind::Enum(..) | TypeDefKind::Struct(..) | TypeDefKind::Foreign(..) => {}
        },
        ItemKind::FuncDef(f) => {
            generate_constraints_fn_def(ctx, PolyvarScope::empty(), f, f.name.id);
        }
        ItemKind::ForeignFuncDecl(f) => {
            let func_node_id = f.name.id;
            let ty_pat = TypeVar::from_node(ctx, f.name.id);

            let ty_func = generate_constraints_func_decl(
                ctx,
                func_node_id,
                PolyvarScope::empty(),
                &f.args,
                &f.ret_type,
            );

            constrain(ctx, ty_pat, ty_func);
        }
    }
}

fn generate_constraints_stmt(
    polyvar_scope: PolyvarScope,
    mode: Mode,
    stmt: Rc<Stmt>,
    ctx: &mut StaticsContext,
) {
    match &*stmt.kind {
        StmtKind::Expr(expr) => {
            generate_constraints_expr(polyvar_scope, mode, expr.clone(), ctx);
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            let ty_pat = TypeVar::from_node(ctx, pat.id);

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_typevar(ctx, ty_ann.clone());
                polyvar_scope.add_polys(&ty_ann);
                generate_constraints_pat(
                    polyvar_scope.clone(),
                    Mode::Ana { expected: ty_ann },
                    pat.clone(),
                    ctx,
                )
            } else {
                generate_constraints_pat(polyvar_scope.clone(), Mode::Syn, pat.clone(), ctx)
            };

            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                ctx,
            );
        }
        StmtKind::Set(lhs, rhs) => {
            let ty_lhs = TypeVar::from_node(ctx, lhs.id);
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, lhs.clone(), ctx);
            let ty_rhs = TypeVar::from_node(ctx, rhs.id);
            generate_constraints_expr(polyvar_scope, Mode::Syn, rhs.clone(), ctx);
            constrain(ctx, ty_lhs, ty_rhs);
        }
        StmtKind::FuncDef(f) => {
            generate_constraints_fn_def(ctx, polyvar_scope, f, f.name.id);
        }
    }
}

fn generate_constraints_expr(
    polyvar_scope: PolyvarScope,
    mode: Mode,
    expr: Rc<Expr>,
    ctx: &mut StaticsContext,
) {
    let node_ty = TypeVar::from_node(ctx, expr.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(ctx, node_ty.clone(), expected),
    };
    match &*expr.kind {
        ExprKind::Unit => {
            constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.id)));
        }
        ExprKind::Int(_) => {
            constrain(ctx, node_ty, TypeVar::make_int(Reason::Node(expr.id)));
        }
        ExprKind::Float(_) => {
            constrain(ctx, node_ty, TypeVar::make_float(Reason::Node(expr.id)));
        }
        ExprKind::Bool(_) => {
            constrain(ctx, node_ty, TypeVar::make_bool(Reason::Node(expr.id)));
        }
        ExprKind::Str(s) => {
            constrain(ctx, node_ty, TypeVar::make_string(Reason::Node(expr.id)));
            let len = ctx.string_constants.len();
            ctx.string_constants.entry(s.clone()).or_insert(len);
        }
        ExprKind::List(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(expr.id).into()));

            let list_decl = ctx
                .global_namespace
                .namespaces
                .get("prelude")
                .and_then(|p| p.declarations.get("list"));

            if let Some(Declaration::Enum(enum_def)) = list_decl {
                constrain(
                    ctx,
                    node_ty,
                    TypeVar::make_nominal(
                        Reason::Node(expr.id),
                        Nominal::Enum(enum_def.clone()),
                        vec![elem_ty.clone()],
                    ),
                );
            } else {
                dbg!(list_decl);
                todo!();
                // TODO: log error
            }

            for expr in exprs {
                generate_constraints_expr(
                    polyvar_scope.clone(),
                    Mode::Ana {
                        expected: elem_ty.clone(),
                    },
                    expr.clone(),
                    ctx,
                );
            }
        }
        ExprKind::Array(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(expr.id).into()));
            constrain(
                ctx,
                node_ty,
                TypeVar::make_nominal(Reason::Node(expr.id), Nominal::Array, vec![elem_ty.clone()]),
            );
            for expr in exprs {
                generate_constraints_expr(
                    polyvar_scope.clone(),
                    Mode::Ana {
                        expected: elem_ty.clone(),
                    },
                    expr.clone(),
                    ctx,
                );
            }
        }
        ExprKind::Identifier(_) => {
            let lookup = ctx.resolution_map.get(&expr.id).cloned();
            if let Some(res) = lookup {
                if let Some(typ) = tyvar_of_declaration(ctx, &res, expr.id, polyvar_scope.clone()) {
                    let typ = typ.instantiate(polyvar_scope, ctx, Prov::Node(expr.id));
                    constrain(ctx, typ, node_ty.clone());
                }
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(ctx, op, expr.id);
            let (ty_left, ty_right, ty_out) = (
                ty_left.instantiate(PolyvarScope::empty(), ctx, Prov::Node(expr.id)),
                ty_right.instantiate(PolyvarScope::empty(), ctx, Prov::Node(expr.id)),
                ty_out.instantiate(PolyvarScope::empty(), ctx, Prov::Node(expr.id)),
            );
            constrain(ctx, ty_out, node_ty);
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::Ana { expected: ty_left },
                left.clone(),
                ctx,
            );
            generate_constraints_expr(
                polyvar_scope,
                Mode::Ana { expected: ty_right },
                right.clone(),
                ctx,
            );
        }
        ExprKind::Block(statements) => {
            if statements.is_empty() {
                constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.id)));
                return;
            }
            for statement in statements[..statements.len() - 1].iter() {
                generate_constraints_stmt(polyvar_scope.clone(), Mode::Syn, statement.clone(), ctx);
            }
            // if last statement is an expression, the block will have that expression's type
            if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().kind {
                generate_constraints_expr(
                    polyvar_scope,
                    Mode::Ana { expected: node_ty },
                    terminal_expr.clone(),
                    ctx,
                )
            } else {
                generate_constraints_stmt(
                    polyvar_scope,
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                    ctx,
                );
                constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.id)))
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::Ana {
                    expected: TypeVar::make_bool(Reason::Node(cond.id)),
                },
                cond.clone(),
                ctx,
            );
            match &expr2 {
                // if-else
                Some(expr2) => {
                    generate_constraints_expr(
                        polyvar_scope.clone(),
                        Mode::Ana {
                            expected: node_ty.clone(),
                        },
                        expr1.clone(),
                        ctx,
                    );
                    generate_constraints_expr(
                        polyvar_scope,
                        Mode::Ana { expected: node_ty },
                        expr2.clone(),
                        ctx,
                    );
                }
                // just if
                None => {
                    generate_constraints_expr(
                        polyvar_scope,
                        Mode::Ana {
                            expected: TypeVar::make_unit(Reason::Node(expr.id)),
                        },
                        expr1.clone(),
                        ctx,
                    );
                    constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.id)))
                }
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::Ana {
                    expected: TypeVar::make_bool(Reason::Node(cond.id)),
                },
                cond.clone(),
                ctx,
            );
            generate_constraints_expr(polyvar_scope, Mode::Syn, expr.clone(), ctx);
            constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.id)))
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = TypeVar::from_node(ctx, scrut.id);
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::Ana {
                    expected: ty_scrutiny.clone(),
                },
                scrut.clone(),
                ctx,
            );
            for arm in arms {
                generate_constraints_pat(
                    polyvar_scope.clone(),
                    Mode::Ana {
                        expected: ty_scrutiny.clone(),
                    },
                    arm.pat.clone(),
                    ctx,
                );
                generate_constraints_expr(
                    polyvar_scope.clone(),
                    Mode::Ana {
                        expected: node_ty.clone(),
                    },
                    arm.expr.clone(),
                    ctx,
                );
            }
        }
        ExprKind::Func(args, out_annot, body) => {
            let func_node_id = expr.id;
            let body_symbol_table = polyvar_scope.new_scope();
            let ty_func = generate_constraints_func_helper(
                ctx,
                func_node_id,
                body_symbol_table,
                args,
                out_annot,
                body,
            );

            constrain(ctx, node_ty, ty_func);
        }
        ExprKind::FuncAp(func, args) => {
            // arguments
            let tys_args: Vec<TypeVar> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown =
                        TypeVar::fresh(ctx, Prov::FuncArg(Box::new(Prov::Node(func.id)), n as u8));
                    generate_constraints_expr(
                        polyvar_scope.clone(),
                        Mode::Ana {
                            expected: unknown.clone(),
                        },
                        arg.clone(),
                        ctx,
                    );
                    unknown
                })
                .collect();

            // body
            let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(Box::new(Prov::Node(func.id))));
            constrain(ctx, ty_body.clone(), node_ty);

            // function type
            let ty_func = TypeVar::make_func(tys_args, ty_body, Reason::Node(expr.id));
            generate_constraints_expr(
                polyvar_scope,
                Mode::Ana {
                    expected: ty_func.clone(),
                },
                func.clone(),
                ctx,
            );

            // println!("funcap: {}", ty_func);
        }
        ExprKind::Tuple(exprs) => {
            let tys = exprs
                .iter()
                .map(|expr| TypeVar::fresh(ctx, Prov::Node(expr.id)))
                .collect();
            constrain(
                ctx,
                node_ty,
                TypeVar::make_tuple(tys, Reason::Node(expr.id)),
            );
            for expr in exprs {
                generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, expr.clone(), ctx);
            }
        }
        ExprKind::MemberAccess(expr, field) => {
            generate_constraints_expr(polyvar_scope, Mode::Syn, expr.clone(), ctx);
            let ty_expr = TypeVar::fresh(ctx, Prov::Node(expr.id));
            if ty_expr.underdetermined() {
                ctx.errors
                    .push(Error::MemberAccessNeedsAnnotation { node_id: expr.id });
                return;
            }
            let Some(inner) = ty_expr.single() else {
                return;
            };
            if let PotentialType::Nominal(_, Nominal::Struct(struct_def), _) = inner {
                let ExprKind::Identifier(field_ident) = &*field.kind else {
                    panic!()
                };
                let ty_field =
                    TypeVar::fresh(ctx, Prov::StructField(field_ident.clone(), struct_def.id));
                constrain(ctx, node_ty.clone(), ty_field);
            }
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, accessed.clone(), ctx);

            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(accessed.id).into()));
            let accessed_ty = TypeVar::from_node(ctx, accessed.id);
            constrain(
                ctx,
                accessed_ty,
                TypeVar::make_nominal(
                    Reason::Node(accessed.id),
                    Nominal::Array,
                    vec![elem_ty.clone()],
                ),
            );
            generate_constraints_expr(
                polyvar_scope,
                Mode::Ana {
                    expected: TypeVar::make_int(Reason::IndexAccess),
                },
                index.clone(),
                ctx,
            );

            constrain(ctx, node_ty, elem_ty);
        }
    }
}

// TODO: code duplication with generate_constraints_fun_decl
fn generate_constraints_func_helper(
    ctx: &mut StaticsContext,
    node_id: NodeId,
    polyvar_scope: PolyvarScope,
    args: &[ArgAnnotated],
    out_annot: &Option<Rc<AstType>>,
    body: &Rc<Expr>,
) -> TypeVar {
    // arguments
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(ctx, arg.id);
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(ctx, arg_annot.id());
                    let arg_annot = ast_type_to_typevar(ctx, arg_annot.clone());
                    constrain(ctx, ty_annot.clone(), arg_annot.clone());
                    polyvar_scope.add_polys(&arg_annot);
                    generate_constraints_pat(
                        polyvar_scope.clone(),
                        Mode::Ana { expected: ty_annot },
                        arg.clone(),
                        ctx,
                    )
                }
                None => {
                    generate_constraints_pat(polyvar_scope.clone(), Mode::Syn, arg.clone(), ctx)
                }
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(Box::new(Prov::Node(node_id))));
    generate_constraints_expr(
        polyvar_scope.clone(),
        Mode::Ana {
            expected: ty_body.clone(),
        },
        body.clone(),
        ctx,
    );
    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_typevar(ctx, out_annot.clone());
        polyvar_scope.add_polys(&out_annot);
        generate_constraints_expr(
            polyvar_scope,
            Mode::Ana {
                expected: out_annot,
            },
            body.clone(),
            ctx,
        );
    }

    TypeVar::make_func(ty_args, ty_body, Reason::Node(node_id))
}

fn generate_constraints_func_decl(
    ctx: &mut StaticsContext,
    node_id: NodeId,
    polyvar_scope: PolyvarScope,
    args: &[ArgAnnotated], // TODO: arguments must be annotated, can't be optional for foreign function decl (or interface function decl)
    out_annot: &Rc<AstType>,
) -> TypeVar {
    // arguments
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(ctx, arg.id);
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(ctx, arg_annot.id());
                    let arg_annot = ast_type_to_typevar(ctx, arg_annot.clone());
                    constrain(ctx, ty_annot.clone(), arg_annot.clone());
                    polyvar_scope.add_polys(&arg_annot);
                    generate_constraints_pat(
                        polyvar_scope.clone(),
                        Mode::Ana { expected: ty_annot },
                        arg.clone(),
                        ctx,
                    )
                }
                None => {
                    generate_constraints_pat(polyvar_scope.clone(), Mode::Syn, arg.clone(), ctx)
                }
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(Box::new(Prov::Node(node_id))));

    let out_annot = ast_type_to_typevar(ctx, out_annot.clone());
    polyvar_scope.add_polys(&out_annot);

    constrain(ctx, ty_body.clone(), out_annot);

    TypeVar::make_func(ty_args, ty_body, Reason::Node(node_id))
}

fn generate_constraints_fn_def(
    ctx: &mut StaticsContext,
    polyvar_scope: PolyvarScope,
    f: &FuncDef,
    id: NodeId,
) {
    let func_node_id = id;
    let ty_fun_name = TypeVar::from_node(ctx, f.name.id);

    let body_symbol_table = polyvar_scope.new_scope();
    let ty_func = generate_constraints_func_helper(
        ctx,
        func_node_id,
        body_symbol_table,
        &f.args,
        &f.ret_type,
        &f.body,
    );

    constrain(ctx, ty_fun_name, ty_func);
}

fn generate_constraints_pat(
    polyvar_scope: PolyvarScope,
    mode: Mode,
    pat: Rc<Pat>,
    ctx: &mut StaticsContext,
) {
    let ty_pat = TypeVar::from_node(ctx, pat.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(ctx, expected, ty_pat.clone()),
    };
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Unit => {
            constrain(ctx, ty_pat, TypeVar::make_unit(Reason::Node(pat.id)));
        }
        PatKind::Int(_) => {
            constrain(ctx, ty_pat, TypeVar::make_int(Reason::Node(pat.id)));
        }
        PatKind::Float(_) => {
            constrain(ctx, ty_pat, TypeVar::make_float(Reason::Node(pat.id)));
        }
        PatKind::Bool(_) => {
            constrain(ctx, ty_pat, TypeVar::make_bool(Reason::Node(pat.id)));
        }
        PatKind::Str(_) => {
            constrain(ctx, ty_pat, TypeVar::make_string(Reason::Node(pat.id)));
        }
        PatKind::Binding(_) => {}
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => TypeVar::from_node(ctx, data.id),
                None => TypeVar::make_unit(Reason::VariantNoData(Box::new(Reason::Node(pat.id)))),
            };
            let mut substitution = BTreeMap::new();
            let ty_enum_instance = {
                if let Some(Declaration::EnumVariant { enum_def, variant }) =
                    ctx.resolution_map.get(&tag.id).cloned()
                {
                    let nparams = enum_def.ty_args.len();
                    let mut params = vec![];
                    for i in 0..nparams {
                        params.push(TypeVar::fresh(
                            ctx,
                            Prov::InstantiateUdtParam(Box::new(Prov::Node(pat.id)), i as u8),
                        ));
                        // TODO: don't do this silly downcast.
                        // ty_args should just be a Vec<Identifier> most likely
                        let TypeKind::Poly(ty_arg, _) = &*enum_def.ty_args[i].kind else {
                            panic!()
                        };
                        substitution.insert(ty_arg.v.clone(), params[i].clone());
                    }
                    let def_type = TypeVar::make_nominal(
                        Reason::UdtDef(Box::new(Reason::Node(pat.id))),
                        Nominal::Enum(enum_def.clone()),
                        params,
                    );

                    let variant_def = &enum_def.variants[variant as usize];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_unit(Reason::VariantNoData(
                            Reason::Node(variant_def.id).into(),
                        )),
                        Some(ty) => ast_type_to_typevar(ctx, ty.clone()),
                    };
                    let variant_data_ty = variant_data_ty.subst(
                        polyvar_scope.clone(),
                        Prov::Node(pat.id),
                        &substitution,
                    );
                    constrain(ctx, ty_data.clone(), variant_data_ty);

                    def_type
                } else {
                    panic!("variant not found");
                }
            };

            constrain(ctx, ty_pat, ty_enum_instance);
            if let Some(data) = data {
                generate_constraints_pat(
                    polyvar_scope,
                    Mode::Ana { expected: ty_data },
                    data.clone(),
                    ctx,
                )
            };
        }
        PatKind::Tuple(pats) => {
            let tys_elements = pats
                .iter()
                .map(|pat| TypeVar::fresh(ctx, Prov::Node(pat.id)))
                .collect();
            constrain(
                ctx,
                ty_pat,
                TypeVar::make_tuple(tys_elements, Reason::Node(pat.id)),
            );
            for pat in pats {
                generate_constraints_pat(polyvar_scope.clone(), Mode::Syn, pat.clone(), ctx)
            }
        }
    }
}

pub(crate) fn monotype_to_typevar(ty: Monotype, reason: Reason) -> TypeVar {
    match ty {
        Monotype::Unit => TypeVar::make_unit(reason),
        Monotype::Int => TypeVar::make_int(reason),
        Monotype::Float => TypeVar::make_float(reason),
        Monotype::Bool => TypeVar::make_bool(reason),
        Monotype::String => TypeVar::make_string(reason),
        Monotype::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|e| monotype_to_typevar(e, reason.clone()))
                .collect();
            TypeVar::make_tuple(elements, reason)
        }
        Monotype::Function(args, out) => {
            let args = args
                .into_iter()
                .map(|a| monotype_to_typevar(a, reason.clone()))
                .collect();
            let out = monotype_to_typevar(*out, reason.clone());
            TypeVar::make_func(args, out, reason.clone())
        }
        Monotype::Nominal(name, params) => {
            let params = params
                .into_iter()
                .map(|p| monotype_to_typevar(p, reason.clone()))
                .collect();
            TypeVar::make_nominal(reason, name, params)
        }
    }
}

pub(crate) fn solved_type_to_typevar(ty: SolvedType, reason: Reason) -> TypeVar {
    match ty {
        SolvedType::Unit => TypeVar::make_unit(reason),
        SolvedType::Int => TypeVar::make_int(reason),
        SolvedType::Float => TypeVar::make_float(reason),
        SolvedType::Bool => TypeVar::make_bool(reason),
        SolvedType::String => TypeVar::make_string(reason),
        SolvedType::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|e| solved_type_to_typevar(e, reason.clone()))
                .collect();
            TypeVar::make_tuple(elements, reason)
        }
        SolvedType::Function(args, out) => {
            let args = args
                .into_iter()
                .map(|a| solved_type_to_typevar(a, reason.clone()))
                .collect();
            let out = solved_type_to_typevar(*out, reason.clone());
            TypeVar::make_func(args, out, reason.clone())
        }
        SolvedType::Nominal(name, params) => {
            let params = params
                .into_iter()
                .map(|p| solved_type_to_typevar(p, reason.clone()))
                .collect();
            TypeVar::make_nominal(reason, name, params)
        }
        SolvedType::Poly(ident, interfaces) => TypeVar::make_poly(reason, ident, interfaces),
    }
}

pub(crate) fn fmt_conflicting_types(types: &[PotentialType], f: &mut dyn Write) -> fmt::Result {
    writeln!(f)?;
    for (i, t) in types.iter().enumerate() {
        if types.len() == 1 {
            write!(f, "{t}")?;
            break;
        }
        if i == 0 {
            write!(f, "\t- {t}")?;
        } else {
            write!(f, "\n\t- {t}")?;
        }
    }
    Ok(())
}

// TODO: there should be a file separate from typecheck that just has stuff pertaining to Types that the whole compiler can use
// type-utils or just types.rs
pub(crate) fn ty_fits_impl_ty(
    ctx: &mut StaticsContext,
    typ: SolvedType,
    impl_ty: SolvedType,
) -> Result<(), (SolvedType, SolvedType)> {
    match (&typ, &impl_ty) {
        (SolvedType::Int, SolvedType::Int)
        | (SolvedType::Bool, SolvedType::Bool)
        | (SolvedType::Float, SolvedType::Float)
        | (SolvedType::String, SolvedType::String)
        | (SolvedType::Unit, SolvedType::Unit) => Ok(()),
        (SolvedType::Tuple(tys1), SolvedType::Tuple(tys2)) => {
            if tys1.len() == tys2.len() {
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone())?;
                }
                Ok(())
            } else {
                Err((typ, impl_ty))
            }
        }
        (SolvedType::Function(args1, out1), SolvedType::Function(args2, out2)) => {
            if args1.len() == args2.len() {
                for (ty1, ty2) in args1.iter().zip(args2.iter()) {
                    ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone())?;
                }
                ty_fits_impl_ty(ctx, *out1.clone(), *out2.clone())
            } else {
                Err((typ, impl_ty))
            }
        }
        (SolvedType::Nominal(ident1, tys1), SolvedType::Nominal(ident2, tys2)) => {
            if ident1 == ident2 && tys1.len() == tys2.len() {
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    let SolvedType::Poly(_, interfaces) = ty2.clone() else {
                        panic!()
                    };
                    if !ty_fits_impl_ty_poly(
                        ctx,
                        ty1.clone(),
                        interfaces.iter().cloned().collect::<BTreeSet<_>>(),
                    ) {
                        return Err((typ, impl_ty));
                    }
                }
                Ok(())
            } else {
                Err((typ, impl_ty))
            }
        }
        (_, SolvedType::Poly(_, interfaces)) => {
            if !ty_fits_impl_ty_poly(
                ctx,
                typ.clone(),
                interfaces.iter().cloned().collect::<BTreeSet<_>>(),
            ) {
                return Err((typ, impl_ty));
            }
            Ok(())
        }
        _ => Err((typ, impl_ty)),
    }
}

fn ty_fits_impl_ty_poly(
    ctx: &mut StaticsContext,
    typ: SolvedType,
    interfaces: BTreeSet<Rc<InterfaceDecl>>,
) -> bool {
    for interface in interfaces {
        if let SolvedType::Poly(_, interfaces2) = &typ {
            // if 'a Interface1 is constrained to [Interfaces...], ignore
            if interfaces2.contains(&interface) {
                return true;
            }
        }
        if let Some(impl_list) = ctx.interface_impls.get(&interface).cloned() {
            // find at least one implementation of interface that matches the type constrained to the interface
            for impl_ in impl_list {
                let impl_ty = ast_type_to_solved_type(ctx, impl_.typ.clone());
                if let Some(impl_ty) = impl_ty {
                    if ty_fits_impl_ty(ctx, typ.clone(), impl_ty).is_ok() {
                        return true;
                    }
                }
            }
        }
    }
    false
}

impl Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let types = self.0.clone_data().types;
        match types.len() {
            0 => write!(f, "?{{}}"),
            1 => write!(f, "{}", types.values().next().unwrap()),
            _ => {
                write!(f, "!{{")?;
                for (i, ty) in types.values().enumerate() {
                    if i > 0 {
                        write!(f, "/ ")?;
                    }
                    write!(f, "{}", ty)?;
                }
                write!(f, "}}")
            }
        }
    }
}

impl Display for PotentialType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PotentialType::Poly(_, ident, interfaces) => {
                write!(f, "'{}", ident)?;
                if !interfaces.is_empty() {
                    write!(f, " ")?;
                    for (i, interface) in interfaces.iter().enumerate() {
                        if i != 0 {
                            write!(f, " + ")?;
                        }
                        write!(f, "{}", interface.name.v)?;
                    }
                }
                Ok(())
            }
            PotentialType::Nominal(_, nominal, params) => {
                if !params.is_empty() {
                    write!(f, "{}<", nominal.name())?;
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", nominal.name())
                }
            }
            PotentialType::Unit(_) => write!(f, "void"),
            PotentialType::Int(_) => write!(f, "int"),
            PotentialType::Float(_) => write!(f, "float"),
            PotentialType::Bool(_) => write!(f, "bool"),
            PotentialType::String(_) => write!(f, "string"),
            PotentialType::Function(_, args, out) => {
                write!(f, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") -> ")?;
                write!(f, "{out}")
            }
            PotentialType::Tuple(_, elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for SolvedType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            SolvedType::Poly(ident, interfaces) => {
                write!(f, "'{}", ident)?;
                if !interfaces.is_empty() {
                    write!(f, " ")?;
                    for (i, interface) in interfaces.iter().enumerate() {
                        if i != 0 {
                            write!(f, " + ")?;
                        }
                        write!(f, "{}", interface.name.v)?;
                    }
                }
                Ok(())
            }
            SolvedType::Nominal(nominal, params) => {
                if !params.is_empty() {
                    write!(f, "{}<", nominal.name())?;
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", nominal.name())
                }
            }
            SolvedType::Unit => write!(f, "void"),
            SolvedType::Int => write!(f, "int"),
            SolvedType::Float => write!(f, "float"),
            SolvedType::Bool => write!(f, "bool"),
            SolvedType::String => write!(f, "string"),
            SolvedType::Function(args, out) => {
                write!(f, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") -> ")?;
                write!(f, "{out}")
            }
            SolvedType::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Display for Monotype {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Monotype::Nominal(nominal, params) => {
                if !params.is_empty() {
                    write!(f, "{}<", nominal.name())?;
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", nominal.name())
                }
            }
            Monotype::Unit => write!(f, "void"),
            Monotype::Int => write!(f, "int"),
            Monotype::Float => write!(f, "float"),
            Monotype::Bool => write!(f, "bool"),
            Monotype::String => write!(f, "string"),
            Monotype::Function(args, out) => {
                write!(f, "fn(")?;
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, ") -> ")?;
                write!(f, "{out}")
            }
            Monotype::Tuple(elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", elem)?;
                }
                write!(f, ")")
            }
        }
    }
}
