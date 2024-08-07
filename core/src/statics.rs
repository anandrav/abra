use crate::ast::{
    ArgAnnotated, AstType, Expr, ExprKind, MatchArm, Node, NodeId, NodeMap, Pat, PatKind, Sources,
    Stmt, StmtKind, Symbol, Toplevel, TypeDefKind, TypeKind,
};
use crate::environment::Environment;
use crate::operators::BinOpcode;
use core::panic;

use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::{self, Write};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TypeVar(UnionFindNode<TypeVarData>);

impl fmt::Display for TypeVar {
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

impl TypeVar {
    pub(crate) fn solution(&self) -> Option<SolvedType> {
        self.0.clone_data().solution()
    }

    fn single(&self) -> Option<PotentialType> {
        let types = self.0.clone_data().types;
        if types.len() == 1 {
            Some(types.values().next().unwrap().clone())
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TypeVarData {
    pub(crate) types: BTreeMap<TypeKey, PotentialType>,
}

impl TypeVarData {
    fn new() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    fn singleton(potential_type: PotentialType) -> Self {
        let mut types = BTreeMap::new();
        types.insert(potential_type.key(), potential_type);
        Self { types }
    }

    pub(crate) fn solution(&self) -> Option<SolvedType> {
        if self.types.len() == 1 {
            self.types.values().next().unwrap().solution()
        } else {
            None
        }
    }

    fn merge(first: Self, second: Self) -> Self {
        let mut merged_types = Self { types: first.types };
        for (_key, t) in second.types {
            merged_types.extend(t);
        }
        merged_types
    }

    fn extend(&mut self, t_other: PotentialType) {
        let key = t_other.key();

        // accumulate provenances and constrain children to each other if applicable
        if let Some(t) = self.types.get_mut(&key) {
            match &t_other {
                PotentialType::Unit(other_provs)
                | PotentialType::Int(other_provs)
                | PotentialType::Float(other_provs)
                | PotentialType::Bool(other_provs)
                | PotentialType::String(other_provs) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                }
                PotentialType::Poly(other_provs, _, _interfaces) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                }
                PotentialType::Function(other_provs, args1, out1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let PotentialType::Function(_, args2, out2) = t {
                        for (arg, arg2) in args1.iter().zip(args2.iter()) {
                            constrain(arg.clone(), arg2.clone());
                        }
                        constrain(out1.clone(), out2.clone());
                    }
                }
                PotentialType::Tuple(other_provs, elems1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let PotentialType::Tuple(_, elems2) = t {
                        for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                            constrain(elem.clone(), elem2.clone());
                        }
                    }
                }
                PotentialType::UdtInstance(other_provs, _, other_tys) => {
                    if let PotentialType::UdtInstance(_, _, tys) = t {
                        if tys.len() == other_tys.len() {
                            for (ty, other_ty) in tys.iter().zip(other_tys.iter()) {
                                constrain(ty.clone(), other_ty.clone());
                            }
                        } else {
                            panic!("should be same length")
                        }
                        t.provs().borrow_mut().extend(other_provs.borrow().clone());
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PotentialType {
    Poly(Provs, Symbol, Vec<Symbol>), // type name, then list of Interfaces it must match
    Unit(Provs),
    Int(Provs),
    Float(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<TypeVar>, TypeVar),
    Tuple(Provs, Vec<TypeVar>),
    UdtInstance(Provs, Symbol, Vec<TypeVar>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SolvedType {
    Poly(Symbol, Vec<Symbol>), // type name, then list of Interfaces it must match
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<SolvedType>, Box<SolvedType>),
    Tuple(Vec<SolvedType>),
    UdtInstance(Symbol, Vec<SolvedType>),
}

impl SolvedType {
    pub(crate) fn instance_type(&self) -> Option<TypeMonomorphized> {
        match self {
            Self::Poly(..) => None,
            Self::Unit => Some(TypeMonomorphized::Unit),
            Self::Int => Some(TypeMonomorphized::Int),
            Self::Float => Some(TypeMonomorphized::Float),
            Self::Bool => Some(TypeMonomorphized::Bool),
            Self::String => Some(TypeMonomorphized::String),
            Self::Function(args, out) => {
                let mut args2: Vec<TypeMonomorphized> = vec![];
                for arg in args {
                    if let Some(arg) = arg.instance_type() {
                        args2.push(arg);
                    } else {
                        return None;
                    }
                }
                let out = out.instance_type()?;
                Some(TypeMonomorphized::Function(args2, out.into()))
            }
            Self::Tuple(elems) => {
                let mut elems2 = vec![];
                for elem in elems {
                    if let Some(elem) = elem.instance_type() {
                        elems2.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(TypeMonomorphized::Tuple(elems2))
            }
            Self::UdtInstance(ident, params) => {
                let mut params2: Vec<TypeMonomorphized> = vec![];
                for param in params {
                    if let Some(param) = param.instance_type() {
                        params2.push(param);
                    } else {
                        return None;
                    }
                }
                Some(TypeMonomorphized::Adt(ident.clone(), params2))
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
            Self::UdtInstance(_, _tys) => false,
        }
    }
}

// This is the fully instantiated AKA monomorphized type of an interface's implementation
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeMonomorphized {
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<TypeMonomorphized>, Box<TypeMonomorphized>),
    Tuple(Vec<TypeMonomorphized>),
    Adt(Symbol, Vec<TypeMonomorphized>),
}

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

// If two types don't share the same key, they must be in conflict
// (If two types share the same key, they may or may not be in conflict)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TypeKey {
    Poly,              // TODO: why isn't the Identifier included here?
    TyApp(Symbol, u8), // u8 represents the number of type params
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(u8), // u8 represents the number of arguments
    Tuple(u8),    // u8 represents the number of elements
}

// Provenances are used to:
// (1) track the origins (plural!) of a type solution
// (2) give the *unique* identity of an unknown type variable (UnifVar) in the SolutionMap
// TODO: Does Prov really need to be that deeply nested? Will there really be FuncArg -> InstantiatedPoly -> BinopLeft -> Node? Or can we simplify here?
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Prov {
    Node(NodeId),    // the type of an expression or statement
    Builtin(String), // a function or constant, which doesn't exist in the AST
    UnderdeterminedCoerceToUnit,

    Alias(Symbol), // TODO add Box<Prov>
    UdtDef(Box<Prov>),

    InstantiateUdtParam(Box<Prov>, u8),
    InstantiatePoly(Box<Prov>, Symbol),
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
    BinopLeft(Box<Prov>),
    BinopRight(Box<Prov>),
    ListElem(Box<Prov>),
    StructField(Symbol, TypeVar),
    IndexAccess,
    VariantNoData(Box<Prov>), // the type of the data of a variant with no data, always Unit.
}

impl Prov {
    // TODO: Can we make this not Optional? Only reason it would fail is if the last prov in the chain is a builtin
    // TODO: remove Builtin prov for this reason, defeats the purpose. Builtins should be declared in the PRELUDE, and that declaration will be the Prov.
    pub(crate) fn get_location(&self) -> Option<NodeId> {
        match self {
            Prov::Node(id) => Some(*id),
            Prov::Builtin(_) => None,
            Prov::UnderdeterminedCoerceToUnit => None,
            Prov::Alias(_) => None,
            Prov::UdtDef(inner)
            | Prov::InstantiateUdtParam(inner, _)
            | Prov::InstantiatePoly(inner, _)
            | Prov::FuncArg(inner, _)
            | Prov::FuncOut(inner)
            | Prov::BinopLeft(inner)
            | Prov::BinopRight(inner)
            | Prov::ListElem(inner)
            | Prov::VariantNoData(inner) => inner.get_location(),
            Prov::StructField(_, _) => None,
            Prov::IndexAccess => None,
        }
    }
}

impl PotentialType {
    pub(crate) fn key(&self) -> TypeKey {
        match self {
            PotentialType::Poly(_, _, _) => TypeKey::Poly,
            PotentialType::Unit(_) => TypeKey::Unit,
            PotentialType::Int(_) => TypeKey::Int,
            PotentialType::Float(_) => TypeKey::Float,
            PotentialType::Bool(_) => TypeKey::Bool,
            PotentialType::String(_) => TypeKey::String,
            PotentialType::Function(_, args, _) => TypeKey::Function(args.len() as u8),
            PotentialType::Tuple(_, elems) => TypeKey::Tuple(elems.len() as u8),
            PotentialType::UdtInstance(_, ident, params) => {
                TypeKey::TyApp(ident.clone(), params.len() as u8)
            }
        }
    }

    pub(crate) fn solution(&self) -> Option<SolvedType> {
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
            Self::UdtInstance(_, ident, params) => {
                let mut params2: Vec<SolvedType> = vec![];
                for param in params {
                    if let Some(param) = param.solution() {
                        params2.push(param);
                    } else {
                        return None;
                    }
                }
                Some(SolvedType::UdtInstance(ident.clone(), params2))
            }
        }
    }

    pub(crate) fn provs(&self) -> &Provs {
        match self {
            Self::Poly(provs, _, _)
            | Self::Unit(provs)
            | Self::Int(provs)
            | Self::Float(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _)
            | Self::UdtInstance(provs, _, _) => provs,
        }
    }

    pub(crate) fn make_unit(prov: Prov) -> PotentialType {
        PotentialType::Unit(provs_singleton(prov))
    }

    pub(crate) fn make_int(prov: Prov) -> PotentialType {
        PotentialType::Int(provs_singleton(prov))
    }

    pub(crate) fn make_float(prov: Prov) -> PotentialType {
        PotentialType::Float(provs_singleton(prov))
    }

    pub(crate) fn make_bool(prov: Prov) -> PotentialType {
        PotentialType::Bool(provs_singleton(prov))
    }

    pub(crate) fn make_string(prov: Prov) -> PotentialType {
        PotentialType::String(provs_singleton(prov))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, prov: Prov) -> PotentialType {
        PotentialType::Function(provs_singleton(prov), args, out)
    }

    pub(crate) fn make_tuple(elems: Vec<TypeVar>, prov: Prov) -> PotentialType {
        PotentialType::Tuple(provs_singleton(prov), elems)
    }

    pub(crate) fn make_poly(prov: Prov, ident: String, interfaces: Vec<String>) -> PotentialType {
        PotentialType::Poly(provs_singleton(prov), ident, interfaces)
    }

    pub(crate) fn make_poly_constrained(
        prov: Prov,
        ident: String,
        interface_ident: String,
    ) -> PotentialType {
        PotentialType::Poly(provs_singleton(prov), ident, vec![interface_ident])
    }

    pub(crate) fn make_def_instance(
        prov: Prov,
        ident: String,
        params: Vec<TypeVar>,
    ) -> PotentialType {
        PotentialType::UdtInstance(provs_singleton(prov), ident, params)
    }
}

impl TypeVar {
    // Creates a clone of a Type with polymorphic variables not in scope with fresh unification variables
    pub(crate) fn instantiate(
        self,
        gamma: Gamma,
        inf_ctx: &mut InferenceContext,
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
                if !gamma.lookup_poly(ident) {
                    let ret = TypeVar::fresh(
                        inf_ctx,
                        Prov::InstantiatePoly(Box::new(prov.clone()), ident.clone()),
                    );
                    let mut extension = Vec::new();
                    for i in interfaces {
                        extension.push((i.clone(), prov.clone()));
                    }
                    inf_ctx
                        .types_constrained_to_interfaces
                        .entry(ret.clone())
                        .or_default()
                        .extend(extension);
                    return ret; // instantiation occurs here
                } else {
                    ty // noop
                }
            }
            PotentialType::UdtInstance(provs, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                PotentialType::UdtInstance(provs, ident, params)
            }
            PotentialType::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                let out = out.instantiate(gamma.clone(), inf_ctx, prov.clone());
                PotentialType::Function(provs, args, out)
            }
            PotentialType::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                PotentialType::Tuple(provs, elems)
            }
        };
        let mut types = BTreeMap::new();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData { types };
        let tvar = TypeVar(UnionFindNode::new(data_instantiated));
        inf_ctx.vars.insert(prov, tvar.clone());
        tvar
    }

    // Creates a *new* Type with polymorphic variabels replaced by subtitutions
    pub(crate) fn subst(
        self,
        gamma: Gamma,
        prov: Prov,
        substitution: &BTreeMap<Symbol, TypeVar>,
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
                PotentialType::UdtInstance(provs, ident, params) => {
                    let params = params
                        .into_iter()
                        .map(|ty| ty.subst(gamma.clone(), prov.clone(), substitution))
                        .collect();
                    PotentialType::UdtInstance(provs, ident, params)
                }
                PotentialType::Function(provs, args, out) => {
                    let args = args
                        .into_iter()
                        .map(|ty| ty.subst(gamma.clone(), prov.clone(), substitution))
                        .collect();
                    let out = out.subst(gamma.clone(), prov, substitution);
                    PotentialType::Function(provs, args, out)
                }
                PotentialType::Tuple(provs, elems) => {
                    let elems = elems
                        .into_iter()
                        .map(|ty| ty.subst(gamma.clone(), prov.clone(), substitution))
                        .collect();
                    PotentialType::Tuple(provs, elems)
                }
            };
            let mut types = BTreeMap::new();
            types.insert(ty.key(), ty);
            let new_data = TypeVarData { types };
            TypeVar(UnionFindNode::new(new_data))
        } else {
            self // noop
        }
    }

    pub(crate) fn from_node(inf_ctx: &mut InferenceContext, id: NodeId) -> TypeVar {
        let prov = Prov::Node(id);
        Self::fresh(inf_ctx, prov)
    }

    pub(crate) fn fresh(inf_ctx: &mut InferenceContext, prov: Prov) -> TypeVar {
        match inf_ctx.vars.get(&prov) {
            Some(ty) => ty.clone(),
            None => {
                let ty = TypeVar(UnionFindNode::new(TypeVarData::new()));
                inf_ctx.vars.insert(prov, ty.clone());
                ty
            }
        }
    }

    fn orphan(potential_type: PotentialType) -> TypeVar {
        TypeVar(UnionFindNode::new(TypeVarData::singleton(potential_type)))
    }

    pub(crate) fn make_unit(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_unit(prov))
    }

    pub(crate) fn make_int(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_int(prov))
    }

    pub(crate) fn make_float(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_float(prov))
    }

    pub(crate) fn make_bool(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_bool(prov))
    }

    pub(crate) fn make_string(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_string(prov))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_func(args, out, prov))
    }

    pub(crate) fn make_tuple(elems: Vec<TypeVar>, prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_tuple(elems, prov))
    }

    pub(crate) fn make_poly(prov: Prov, ident: String, interfaces: Vec<String>) -> TypeVar {
        Self::orphan(PotentialType::make_poly(prov, ident, interfaces))
    }

    pub(crate) fn make_poly_constrained(
        prov: Prov,
        ident: String,
        interface_ident: String,
    ) -> TypeVar {
        Self::orphan(PotentialType::make_poly_constrained(
            prov,
            ident,
            interface_ident,
        ))
    }

    pub(crate) fn make_def_instance(prov: Prov, ident: String, params: Vec<TypeVar>) -> TypeVar {
        Self::orphan(PotentialType::make_def_instance(prov, ident, params))
    }

    // return true if the type is an adt with at least one parameter instantiated
    // this is used to see if an implementation of an interface is for an instantiated adt, which is not allowed
    // example: implement ToString for list<int> rather than list<'a>
    pub(crate) fn is_instantiated_adt(&self) -> bool {
        let Some(ty) = self.single() else {
            return false;
        };
        match ty {
            // return true if an adt with at least one parameter instantiated
            PotentialType::UdtInstance(_, _, tys) => !tys
                .iter()
                .all(|ty| matches!(ty.single(), Some(PotentialType::Poly(..)))),
            _ => false,
        }
    }

    pub(crate) fn underdetermined(&self) -> bool {
        self.0.with_data(|data| data.types.is_empty())
    }
}

fn types_of_binop(opcode: &BinOpcode, id: NodeId) -> (TypeVar, TypeVar, TypeVar) {
    let prov_left = Prov::BinopLeft(Prov::Node(id).into());
    let prov_right = Prov::BinopRight(Prov::Node(id).into());
    let prov_out = Prov::Node(id);
    match opcode {
        BinOpcode::And | BinOpcode::Or => (
            TypeVar::make_bool(prov_left),
            TypeVar::make_bool(prov_right),
            TypeVar::make_bool(prov_out),
        ),
        BinOpcode::Add
        | BinOpcode::Subtract
        | BinOpcode::Multiply
        | BinOpcode::Divide
        | BinOpcode::Pow => {
            let ty_left =
                TypeVar::make_poly_constrained(prov_left, "a".to_owned(), "Num".to_owned());
            let ty_right =
                TypeVar::make_poly_constrained(prov_right, "a".to_owned(), "Num".to_owned());
            let ty_out = TypeVar::make_poly_constrained(prov_out, "a".to_owned(), "Num".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            constrain(ty_left.clone(), ty_out.clone());
            (ty_left, ty_right, ty_out)
        }
        BinOpcode::Mod => (
            TypeVar::make_int(prov_left),
            TypeVar::make_int(prov_right),
            TypeVar::make_int(prov_out),
        ),
        BinOpcode::LessThan
        | BinOpcode::GreaterThan
        | BinOpcode::LessThanOrEqual
        | BinOpcode::GreaterThanOrEqual => {
            let ty_left =
                TypeVar::make_poly_constrained(prov_left, "a".to_owned(), "Num".to_owned());
            let ty_right =
                TypeVar::make_poly_constrained(prov_right, "a".to_owned(), "Num".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            let ty_out = TypeVar::make_bool(prov_out);
            (ty_left, ty_right, ty_out)
        }
        BinOpcode::Concat => (
            TypeVar::make_string(prov_left),
            TypeVar::make_string(prov_right),
            TypeVar::make_string(prov_out),
        ),
        BinOpcode::Equals => {
            let ty_left =
                TypeVar::make_poly_constrained(prov_left, "a".to_owned(), "Equals".to_owned());
            let ty_right =
                TypeVar::make_poly_constrained(prov_right, "a".to_owned(), "Equals".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            (ty_left, ty_right, TypeVar::make_bool(prov_out))
        }
    }
}

fn ast_type_to_statics_type_interface(
    inf_ctx: &mut InferenceContext,
    ast_type: Rc<AstType>,
    interface_ident: Option<&String>,
) -> TypeVar {
    match &*ast_type.typekind {
        TypeKind::Poly(ident, interfaces) => {
            TypeVar::make_poly(Prov::Node(ast_type.id()), ident.clone(), interfaces.clone())
        }
        TypeKind::Alias(ident) => {
            if let Some(interface_ident) = interface_ident {
                if ident == "self" {
                    TypeVar::make_poly_constrained(
                        Prov::Node(ast_type.id()),
                        "a".to_string(),
                        interface_ident.clone(),
                    )
                } else {
                    TypeVar::fresh(inf_ctx, Prov::Alias(ident.clone()))
                }
            } else {
                TypeVar::fresh(inf_ctx, Prov::Alias(ident.clone()))
            }
        }
        TypeKind::Ap(ident, params) => TypeVar::make_def_instance(
            Prov::Node(ast_type.id()),
            ident.clone(),
            params
                .iter()
                .map(|param| {
                    ast_type_to_statics_type_interface(inf_ctx, param.clone(), interface_ident)
                })
                .collect(),
        ),
        TypeKind::Unit => TypeVar::make_unit(Prov::Node(ast_type.id())),
        TypeKind::Int => TypeVar::make_int(Prov::Node(ast_type.id())),
        TypeKind::Float => TypeVar::make_float(Prov::Node(ast_type.id())),
        TypeKind::Bool => TypeVar::make_bool(Prov::Node(ast_type.id())),
        TypeKind::Str => TypeVar::make_string(Prov::Node(ast_type.id())),
        TypeKind::Function(lhs, rhs) => TypeVar::make_func(
            lhs.iter()
                .map(|t| ast_type_to_statics_type_interface(inf_ctx, t.clone(), interface_ident))
                .collect(),
            ast_type_to_statics_type_interface(inf_ctx, rhs.clone(), interface_ident),
            Prov::Node(ast_type.id()),
        ),
        TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_statics_type_interface(
                    inf_ctx,
                    t.clone(),
                    interface_ident,
                ));
            }
            TypeVar::make_tuple(statics_types, Prov::Node(ast_type.id()))
        }
    }
}

fn ast_type_to_statics_type(inf_ctx: &mut InferenceContext, ast_type: Rc<AstType>) -> TypeVar {
    ast_type_to_statics_type_interface(inf_ctx, ast_type, None)
}

pub(crate) type Provs = RefCell<BTreeSet<Prov>>;

pub(crate) fn provs_singleton(prov: Prov) -> Provs {
    let mut set = BTreeSet::new();
    set.insert(prov);
    RefCell::new(set)
}

#[derive(Default, Debug)]
pub(crate) struct InferenceContext {
    // unification variables (skolems) which must be solved
    pub(crate) vars: HashMap<Prov, TypeVar>,

    // ADT definitions
    pub(crate) adt_defs: HashMap<Symbol, AdtDef>,
    // map from variant names to ADT names
    variants_to_adt: HashMap<Symbol, Symbol>,

    // struct definitions
    pub(crate) struct_defs: HashMap<Symbol, StructDef>,

    // function definition locations
    pub(crate) fun_defs: HashMap<Symbol, Rc<Stmt>>,

    // BOOKKEEPING

    // name resolutions
    pub(crate) name_resolutions: HashMap<NodeId, Resolution>,
    // interface definitions
    interface_defs: HashMap<Symbol, InterfaceDef>,
    // map from methods to interface names
    pub(crate) method_to_interface: HashMap<Symbol, Symbol>,
    // map from interface name to list of implementations
    pub(crate) interface_impls: BTreeMap<Symbol, Vec<InterfaceImpl>>,

    // ADDITIONAL CONSTRAINTS
    // map from types to interfaces they have been constrained to
    types_constrained_to_interfaces: BTreeMap<TypeVar, Vec<(Symbol, Prov)>>,
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
    interface_impl_for_instantiated_adt: Vec<NodeId>,
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

impl InferenceContext {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    pub(crate) fn adt_def_of_variant(&self, variant: &Symbol) -> Option<AdtDef> {
        let adt_name = self.variants_to_adt.get(variant)?;
        self.adt_defs.get(adt_name).cloned()
    }

    pub(crate) fn interface_def_of_ident(&self, ident: &Symbol) -> Option<InterfaceDef> {
        self.interface_defs.get(ident).cloned()
    }

    pub(crate) fn variants_of_adt(&self, adt: &Symbol) -> Vec<Symbol> {
        self.adt_defs
            .get(adt)
            .unwrap()
            .variants
            .iter()
            .map(|v| v.ctor.clone())
            .collect()
    }

    pub(crate) fn solution_of_node(&self, id: NodeId) -> Option<SolvedType> {
        let prov = Prov::Node(id);
        match self.vars.get(&prov) {
            Some(unifvar) => unifvar.solution(),
            None => None,
        }
    }
}

fn constrain(mut expected: TypeVar, mut actual: TypeVar) {
    expected.0.union_with(&mut actual.0, TypeVarData::merge);
}

#[derive(Debug, Clone)]
pub(crate) enum Resolution {
    Node(NodeId),
    Builtin(Symbol),
}

// TODO: rename to TypeEnv
#[derive(Clone)]
pub(crate) struct Gamma {
    var_to_type: Environment<Symbol, TypeVar>,
    ty_vars_in_scope: Environment<Symbol, ()>,

    var_declarations: Environment<Symbol, Resolution>,
}
impl Gamma {
    pub(crate) fn empty() -> Self {
        Self {
            var_to_type: Environment::empty(),
            ty_vars_in_scope: Environment::empty(),

            var_declarations: Environment::empty(),
        }
    }

    pub(crate) fn extend(&self, ident: Symbol, ty: TypeVar) {
        self.var_to_type.extend(ident.clone(), ty);
    }

    pub(crate) fn extend_declaration(&self, symbol: Symbol, resolution: Resolution) {
        self.var_declarations.extend(symbol, resolution);
    }

    pub(crate) fn lookup_declaration(&self, symbol: &Symbol) -> Option<Resolution> {
        self.var_declarations.lookup(symbol)
    }

    pub(crate) fn add_polys(&self, ty: &TypeVar) {
        let Some(ty) = ty.single() else {
            return;
        };
        match ty {
            PotentialType::Poly(_, ident, _interfaces) => {
                self.ty_vars_in_scope.extend(ident.clone(), ());
            }
            PotentialType::UdtInstance(_, _, params) => {
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

    pub(crate) fn lookup(&self, id: &Symbol) -> Option<TypeVar> {
        self.var_to_type.lookup(id)
    }

    pub(crate) fn lookup_poly(&self, id: &Symbol) -> bool {
        self.ty_vars_in_scope.lookup(id).is_some()
    }

    pub(crate) fn new_scope(&self) -> Self {
        Self {
            var_to_type: self.var_to_type.new_scope(),
            ty_vars_in_scope: self.ty_vars_in_scope.new_scope(),

            var_declarations: self.var_declarations.new_scope(),
        }
    }
}

// TODO: make a macro for these builtins
pub(crate) fn make_new_gamma() -> Gamma {
    let gamma = Gamma::empty();
    let ident = "newline".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_string(Prov::Builtin("newline: string".to_string())),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));
    let ident = "print_string".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![TypeVar::make_string(Prov::FuncArg(
                Box::new(Prov::Builtin("print_string: string -> void".to_string())),
                0,
            ))],
            TypeVar::make_unit(Prov::FuncOut(Box::new(Prov::Builtin(
                "print_string: string -> void".to_string(),
            )))),
            Prov::Builtin("print_string: string -> void".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));
    let ident = "equals_int".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(
                    Box::new(Prov::Builtin("equals_int: (int, int) -> bool".to_string())),
                    0,
                )),
                TypeVar::make_int(Prov::FuncArg(
                    Box::new(Prov::Builtin("equals_int: (int, int) -> bool".to_string())),
                    1,
                )),
            ],
            TypeVar::make_bool(Prov::FuncOut(Box::new(Prov::Builtin(
                "equals_int: (int, int) -> bool".to_string(),
            )))),
            Prov::Builtin("equals_int: (int, int) -> bool".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "equals_string".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "equals_string: (string, string) -> bool".to_string(),
                    )),
                    0,
                )),
                TypeVar::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "equals_string: (string, string) -> bool".to_string(),
                    )),
                    1,
                )),
            ],
            TypeVar::make_bool(Prov::FuncOut(Box::new(Prov::Builtin(
                "equals_string: (string, string) -> bool".to_string(),
            )))),
            Prov::Builtin("equals_string: (string, string) -> bool".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "int_to_string".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![TypeVar::make_int(Prov::FuncArg(
                Box::new(Prov::Builtin("int_to_string: int -> string".to_string())),
                0,
            ))],
            TypeVar::make_string(Prov::FuncOut(Box::new(Prov::Builtin(
                "int_to_string: int -> string".to_string(),
            )))),
            Prov::Builtin("int_to_string: int -> string".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "float_to_string".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![TypeVar::make_float(Prov::FuncArg(
                Box::new(Prov::Builtin(
                    "float_to_string: float -> string".to_string(),
                )),
                0,
            ))],
            TypeVar::make_string(Prov::FuncOut(Box::new(Prov::Builtin(
                "float_to_string: float -> string".to_string(),
            )))),
            Prov::Builtin("float_to_string: float -> string".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "to_float".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![TypeVar::make_int(Prov::FuncArg(
                Box::new(Prov::Builtin("to_float: int -> float".to_string())),
                0,
            ))],
            TypeVar::make_float(Prov::FuncOut(Box::new(Prov::Builtin(
                "to_float: int -> float".to_string(),
            )))),
            Prov::Builtin("to_float: int -> float".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "round".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![TypeVar::make_float(Prov::FuncArg(
                Box::new(Prov::Builtin("round: float -> int".to_string())),
                0,
            ))],
            TypeVar::make_int(Prov::FuncOut(Box::new(Prov::Builtin(
                "round: float -> int".to_string(),
            )))),
            Prov::Builtin("round: float -> int".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "append_strings".to_owned();
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "append_strings: (string, string) -> string".to_string(),
                    )),
                    0,
                )),
                TypeVar::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "append_strings: (string, string) -> string".to_string(),
                    )),
                    1,
                )),
            ],
            TypeVar::make_string(Prov::FuncOut(Box::new(Prov::Builtin(
                "append_strings: (string, string) -> string".to_string(),
            )))),
            Prov::Builtin("append_strings: (string, string) -> string".to_string()),
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "add_int".to_owned();
    let prov = Prov::Builtin("add_int: (int, int) -> int".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_int(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "minus_int".to_owned();
    let prov = Prov::Builtin("minus_int: (int, int) -> int".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_int(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "multiply_int".to_owned();
    let prov = Prov::Builtin("multiply_int: (int, int) -> int".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_int(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "divide_int".to_owned();
    let prov = Prov::Builtin("divide_int: (int, int) -> int".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_int(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "pow_int".to_owned();
    let prov = Prov::Builtin("pow_int: (int, int) -> int".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_int(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "less_than_int".to_owned();
    let prov = Prov::Builtin("less_than_int: (int, int) -> bool".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_bool(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "add_float".to_owned();
    let prov = Prov::Builtin("add_float: (float, float) -> float".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_float(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "minus_float".to_owned();
    let prov = Prov::Builtin("minus_float: (float, float) -> float".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_float(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "multiply_float".to_owned();
    let prov = Prov::Builtin("multiply_float: (float, float) -> float".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_float(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "divide_float".to_owned();
    let prov = Prov::Builtin("divide_float: (float, float) -> float".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_float(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "pow_float".to_owned();
    let prov = Prov::Builtin("pow_float: (float, float) -> float".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_float(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "sqrt_float".to_owned();
    let prov = Prov::Builtin("sqrt_float: (float) -> float".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0))],
            TypeVar::make_float(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "less_than_float".to_owned();
    let prov = Prov::Builtin("less_than_float: (float, float) -> bool".to_string());
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                TypeVar::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            TypeVar::make_bool(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "append".to_owned();
    let prov = Prov::Builtin("append: (array<'a>, 'a) -> void".to_string());
    let ty_elem = TypeVar::make_poly(
        Prov::FuncArg(prov.clone().into(), 1),
        "'a".to_string(),
        vec![],
    );
    let ty_arr = TypeVar::make_def_instance(
        Prov::FuncArg(prov.clone().into(), 0),
        "array".to_string(),
        vec![TypeVar::make_poly(
            Prov::FuncArg(prov.clone().into(), 1),
            "'a".to_string(),
            vec![],
        )],
    );
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![ty_arr.clone(), ty_elem],
            TypeVar::make_unit(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "len".to_owned();
    let prov = Prov::Builtin("len: (array<'a>) -> int".to_string());
    let ty_arr = TypeVar::make_def_instance(
        Prov::FuncArg(prov.clone().into(), 0),
        "array".to_string(),
        vec![TypeVar::make_poly(
            Prov::FuncArg(prov.clone().into(), 1),
            "'a".to_string(),
            vec![],
        )],
    );
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![ty_arr.clone()],
            TypeVar::make_int(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    let ident = "prov".to_owned();
    let prov = Prov::Builtin("pop: (array<'a>) -> void".to_string());
    let ty_arr = TypeVar::make_def_instance(
        Prov::FuncArg(prov.clone().into(), 0),
        "array".to_string(),
        vec![TypeVar::make_poly(
            Prov::FuncArg(prov.clone().into(), 1),
            "'a".to_string(),
            vec![],
        )],
    );
    gamma.extend(
        ident.clone(),
        TypeVar::make_func(
            vec![ty_arr.clone()],
            TypeVar::make_unit(Prov::FuncOut(prov.clone().into())),
            prov,
        ),
    );
    gamma.extend_declaration(ident.clone(), Resolution::Builtin(ident));

    gamma
}

#[derive(Debug, Clone)]
pub(crate) enum Mode {
    Syn,
    Ana { expected: TypeVar },
}

pub(crate) fn generate_constraints_expr(
    gamma: Gamma,
    mode: Mode,
    expr: Rc<Expr>,
    inf_ctx: &mut InferenceContext,
) {
    let node_ty = TypeVar::from_node(inf_ctx, expr.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(node_ty.clone(), expected),
    };
    match &*expr.exprkind {
        ExprKind::Unit => {
            constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)));
        }
        ExprKind::Int(_) => {
            constrain(node_ty, TypeVar::make_int(Prov::Node(expr.id)));
        }
        ExprKind::Float(_) => {
            constrain(node_ty, TypeVar::make_float(Prov::Node(expr.id)));
        }
        ExprKind::Bool(_) => {
            constrain(node_ty, TypeVar::make_bool(Prov::Node(expr.id)));
        }
        ExprKind::Str(_) => {
            constrain(node_ty, TypeVar::make_string(Prov::Node(expr.id)));
        }
        ExprKind::List(exprs) => {
            let elem_ty = TypeVar::fresh(inf_ctx, Prov::ListElem(Prov::Node(expr.id).into()));
            constrain(
                node_ty,
                TypeVar::make_def_instance(
                    Prov::Node(expr.id),
                    "list".to_owned(),
                    vec![elem_ty.clone()],
                ),
            );
            for expr in exprs {
                generate_constraints_expr(
                    gamma.clone(),
                    Mode::Ana {
                        expected: elem_ty.clone(),
                    },
                    expr.clone(),
                    inf_ctx,
                );
            }
        }
        ExprKind::Array(exprs) => {
            let elem_ty = TypeVar::fresh(inf_ctx, Prov::ListElem(Prov::Node(expr.id).into()));
            constrain(
                node_ty,
                TypeVar::make_def_instance(
                    Prov::Node(expr.id),
                    "array".to_owned(),
                    vec![elem_ty.clone()],
                ),
            );
            for expr in exprs {
                generate_constraints_expr(
                    gamma.clone(),
                    Mode::Ana {
                        expected: elem_ty.clone(),
                    },
                    expr.clone(),
                    inf_ctx,
                );
            }
        }
        ExprKind::Var(symbol) => {
            let lookup = gamma.lookup_declaration(symbol);
            if let Some(resolution) = lookup {
                inf_ctx.name_resolutions.insert(expr.id, resolution);
            }
            let lookup = gamma.lookup(symbol);
            if let Some(typ) = lookup {
                // replace polymorphic types with unifvars if necessary
                let typ = typ.instantiate(gamma, inf_ctx, Prov::Node(expr.id));
                constrain(typ, node_ty);
                return;
            }
            // TODO: this is incredibly hacky. No respect for scope at all... Should be added at the toplevel with Effects at the least...
            let adt_def = inf_ctx.adt_def_of_variant(symbol);
            if let Some(adt_def) = adt_def {
                let nparams = adt_def.params.len();
                let mut params = vec![];
                let mut substitution = BTreeMap::new();
                for i in 0..nparams {
                    params.push(TypeVar::fresh(
                        inf_ctx,
                        Prov::InstantiateUdtParam(Box::new(Prov::Node(expr.id)), i as u8),
                    ));
                    substitution.insert(adt_def.params[i].clone(), params[i].clone());
                }
                let def_type = TypeVar::make_def_instance(
                    Prov::UdtDef(Box::new(Prov::Node(expr.id))),
                    adt_def.name,
                    params,
                );

                let the_variant = adt_def.variants.iter().find(|v| v.ctor == *symbol).unwrap();
                if let Some(PotentialType::Unit(_)) = the_variant.data.single() {
                    constrain(node_ty, def_type);
                } else if let Some(PotentialType::Tuple(_, elems)) = &the_variant.data.single() {
                    let args = elems
                        .iter()
                        .map(|e| {
                            e.clone()
                                .subst(gamma.clone(), Prov::Node(expr.id), &substitution)
                        })
                        .collect();
                    constrain(
                        node_ty,
                        TypeVar::make_func(args, def_type, Prov::Node(expr.id)),
                    );
                } else {
                    constrain(
                        node_ty,
                        TypeVar::make_func(
                            vec![the_variant.data.clone().subst(
                                gamma,
                                Prov::Node(expr.id),
                                &substitution,
                            )],
                            def_type,
                            Prov::Node(expr.id),
                        ),
                    );
                }
                return;
            }
            let struct_def = inf_ctx.struct_defs.get(symbol).cloned();
            if let Some(struct_def) = struct_def {
                let nparams = struct_def.params.len();
                let mut params = vec![];
                let mut substitution = BTreeMap::new();
                for i in 0..nparams {
                    params.push(TypeVar::fresh(
                        inf_ctx,
                        Prov::InstantiateUdtParam(Box::new(Prov::Node(expr.id)), i as u8),
                    ));
                    substitution.insert(struct_def.params[i].clone(), params[i].clone());
                }
                let def_type = TypeVar::make_def_instance(
                    Prov::UdtDef(Box::new(Prov::Node(expr.id))),
                    struct_def.name.clone(),
                    params,
                );
                let fields = struct_def
                    .fields
                    .iter()
                    .map(|f| {
                        f.ty.clone()
                            .subst(gamma.clone(), Prov::Node(expr.id), &substitution)
                    })
                    .collect();
                constrain(
                    node_ty,
                    TypeVar::make_func(fields, def_type, Prov::Node(expr.id)),
                );
                return;
            }
            inf_ctx.unbound_vars.insert(expr.id());
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op, expr.id);
            let (ty_left, ty_right, ty_out) = (
                ty_left.instantiate(gamma.clone(), inf_ctx, Prov::Node(expr.id)),
                ty_right.instantiate(gamma.clone(), inf_ctx, Prov::Node(expr.id)),
                ty_out.instantiate(gamma.clone(), inf_ctx, Prov::Node(expr.id)),
            );
            constrain(ty_out, node_ty);
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana { expected: ty_left },
                left.clone(),
                inf_ctx,
            );
            generate_constraints_expr(
                gamma,
                Mode::Ana { expected: ty_right },
                right.clone(),
                inf_ctx,
            );
        }
        ExprKind::Block(statements) => {
            if statements.is_empty() {
                constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)));
                return;
            }
            let new_gamma = gamma.new_scope();
            for statement in statements[..statements.len() - 1].iter() {
                generate_constraints_stmt(
                    new_gamma.clone(),
                    Mode::Syn,
                    statement.clone(),
                    inf_ctx,
                    true,
                );
            }
            // if last statement is an expression, the block will have that expression's type
            if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().stmtkind {
                generate_constraints_expr(
                    new_gamma,
                    Mode::Ana { expected: node_ty },
                    terminal_expr.clone(),
                    inf_ctx,
                )
            } else {
                generate_constraints_stmt(
                    new_gamma,
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                    inf_ctx,
                    true,
                );
                constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: TypeVar::make_bool(Prov::Node(cond.id)),
                },
                cond.clone(),
                inf_ctx,
            );
            match &expr2 {
                // if-else
                Some(expr2) => {
                    generate_constraints_expr(
                        gamma.clone(),
                        Mode::Ana {
                            expected: node_ty.clone(),
                        },
                        expr1.clone(),
                        inf_ctx,
                    );
                    generate_constraints_expr(
                        gamma,
                        Mode::Ana { expected: node_ty },
                        expr2.clone(),
                        inf_ctx,
                    );
                }
                // just if
                None => {
                    generate_constraints_expr(
                        gamma,
                        Mode::Ana {
                            expected: TypeVar::make_unit(Prov::Node(expr.id)),
                        },
                        expr1.clone(),
                        inf_ctx,
                    );
                    constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
                }
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: TypeVar::make_bool(Prov::Node(cond.id)),
                },
                cond.clone(),
                inf_ctx,
            );
            generate_constraints_expr(gamma, Mode::Syn, expr.clone(), inf_ctx);
            constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = TypeVar::from_node(inf_ctx, scrut.id);
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: ty_scrutiny.clone(),
                },
                scrut.clone(),
                inf_ctx,
            );
            for arm in arms {
                let new_gamma = gamma.new_scope();
                generate_constraints_pat(
                    new_gamma.clone(),
                    Mode::Ana {
                        expected: ty_scrutiny.clone(),
                    },
                    arm.pat.clone(),
                    inf_ctx,
                );
                generate_constraints_expr(
                    new_gamma,
                    Mode::Ana {
                        expected: node_ty.clone(),
                    },
                    arm.expr.clone(),
                    inf_ctx,
                );
            }
        }
        ExprKind::Func(args, out_annot, body) => {
            let func_node_id = expr.id;
            let body_gamma = gamma.new_scope();
            let ty_func = generate_constraints_func_helper(
                inf_ctx,
                func_node_id,
                body_gamma,
                args,
                out_annot,
                body,
            );

            constrain(node_ty, ty_func);
        }
        ExprKind::FuncAp(func, args) => {
            // arguments
            let tys_args: Vec<TypeVar> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = TypeVar::fresh(
                        inf_ctx,
                        Prov::FuncArg(Box::new(Prov::Node(func.id)), n as u8),
                    );
                    generate_constraints_expr(
                        gamma.clone(),
                        Mode::Ana {
                            expected: unknown.clone(),
                        },
                        arg.clone(),
                        inf_ctx,
                    );
                    unknown
                })
                .collect();

            // body
            let ty_body = TypeVar::fresh(inf_ctx, Prov::FuncOut(Box::new(Prov::Node(func.id))));
            constrain(ty_body.clone(), node_ty);

            // function type
            let ty_func = TypeVar::make_func(tys_args, ty_body, Prov::Node(expr.id));
            generate_constraints_expr(
                gamma,
                Mode::Ana { expected: ty_func },
                func.clone(),
                inf_ctx,
            );
        }
        ExprKind::Tuple(exprs) => {
            let tys = exprs
                .iter()
                .map(|expr| TypeVar::fresh(inf_ctx, Prov::Node(expr.id)))
                .collect();
            constrain(node_ty, TypeVar::make_tuple(tys, Prov::Node(expr.id)));
            for expr in exprs {
                generate_constraints_expr(gamma.clone(), Mode::Syn, expr.clone(), inf_ctx);
            }
        }
        ExprKind::FieldAccess(expr, field) => {
            generate_constraints_expr(gamma, Mode::Syn, expr.clone(), inf_ctx);
            let ty_expr = TypeVar::fresh(inf_ctx, Prov::Node(expr.id));
            if ty_expr.underdetermined() {
                inf_ctx.annotation_needed.insert(expr.id);
                return;
            }
            let Some(inner) = ty_expr.single() else {
                return;
            };
            if let PotentialType::UdtInstance(_, ident, _) = inner {
                if let Some(struct_def) = inf_ctx.struct_defs.get(&ident) {
                    let ty_struct = TypeVar::from_node(inf_ctx, struct_def.location);
                    let ExprKind::Var(field_ident) = &*field.exprkind else {
                        inf_ctx.field_not_ident.insert(field.id);
                        return;
                    };
                    let ty_field =
                        TypeVar::fresh(inf_ctx, Prov::StructField(field_ident.clone(), ty_struct));
                    constrain(node_ty.clone(), ty_field);
                    return;
                }
            }

            inf_ctx.types_that_must_be_structs.insert(ty_expr, expr.id);
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(gamma.clone(), Mode::Syn, accessed.clone(), inf_ctx);

            let elem_ty = TypeVar::fresh(inf_ctx, Prov::ListElem(Prov::Node(accessed.id).into()));
            let accessed_ty = TypeVar::from_node(inf_ctx, accessed.id);
            constrain(
                accessed_ty,
                TypeVar::make_def_instance(
                    Prov::Node(accessed.id),
                    "array".to_owned(),
                    vec![elem_ty.clone()],
                ),
            );
            generate_constraints_expr(
                gamma,
                Mode::Ana {
                    expected: TypeVar::make_int(Prov::IndexAccess),
                },
                index.clone(),
                inf_ctx,
            );

            constrain(node_ty, elem_ty);
        }
    }
}

fn generate_constraints_func_helper(
    inf_ctx: &mut InferenceContext,
    node_id: NodeId,
    gamma: Gamma,
    args: &[ArgAnnotated],
    out_annot: &Option<Rc<AstType>>,
    body: &Rc<Expr>,
) -> TypeVar {
    // arguments
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(inf_ctx, arg.id);
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(inf_ctx, arg_annot.id());
                    let arg_annot = ast_type_to_statics_type(inf_ctx, arg_annot.clone());
                    constrain(ty_annot.clone(), arg_annot.clone());
                    gamma.add_polys(&arg_annot);
                    generate_constraints_pat(
                        gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                        Mode::Ana { expected: ty_annot },
                        arg.clone(),
                        inf_ctx,
                    )
                }
                None => generate_constraints_pat(gamma.clone(), Mode::Syn, arg.clone(), inf_ctx),
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(inf_ctx, Prov::FuncOut(Box::new(Prov::Node(node_id))));
    generate_constraints_expr(
        gamma.clone(),
        Mode::Ana {
            expected: ty_body.clone(),
        },
        body.clone(),
        inf_ctx,
    );
    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_statics_type(inf_ctx, out_annot.clone());
        gamma.add_polys(&out_annot);
        generate_constraints_expr(
            gamma,
            Mode::Ana {
                expected: out_annot,
            },
            body.clone(),
            inf_ctx,
        );
    }

    TypeVar::make_func(ty_args, ty_body, Prov::Node(node_id))
}

pub(crate) fn generate_constraints_stmt(
    gamma: Gamma,
    mode: Mode,
    stmt: Rc<Stmt>,
    inf_ctx: &mut InferenceContext,
    add_to_gamma: bool,
) {
    match &*stmt.stmtkind {
        StmtKind::InterfaceDef(..) => {}
        StmtKind::InterfaceImpl(ident, typ, statements) => {
            let typ = ast_type_to_statics_type(inf_ctx, typ.clone());

            if let Some(interface_def) = inf_ctx.interface_def_of_ident(ident) {
                for statement in statements {
                    let StmtKind::FuncDef(pat, _args, _out, _body) = &*statement.stmtkind else {
                        continue;
                    };
                    let method_name = pat.patkind.get_identifier_of_variable();
                    if let Some(interface_method) =
                        interface_def.methods.iter().find(|m| m.name == method_name)
                    {
                        let mut substitution = BTreeMap::new();
                        substitution.insert("a".to_string(), typ.clone());

                        let expected = interface_method.ty.clone().subst(
                            gamma.clone(),
                            Prov::Node(stmt.id),
                            &substitution,
                        );

                        constrain(expected, TypeVar::from_node(inf_ctx, pat.id));

                        generate_constraints_stmt(
                            gamma.clone(),
                            Mode::Syn,
                            statement.clone(),
                            inf_ctx,
                            false,
                        );
                    } else {
                        inf_ctx
                            .interface_impl_extra_method
                            .entry(stmt.id)
                            .or_default()
                            .push(statement.id);
                    }
                }
                for interface_method in interface_def.methods {
                    if !statements.iter().any(|stmt| match &*stmt.stmtkind {
                        StmtKind::FuncDef(pat, _args, _out, _body) => {
                            pat.patkind.get_identifier_of_variable() == interface_method.name
                        }
                        _ => false,
                    }) {
                        inf_ctx
                            .interface_impl_missing_method
                            .entry(stmt.id)
                            .or_default()
                            .push(interface_method.name.clone());
                    }
                }
            } else {
                inf_ctx.unbound_interfaces.insert(stmt.id);
            }
        }
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(ident, ty) => {
                let left = TypeVar::fresh(inf_ctx, Prov::Alias(ident.clone()));
                let right = ast_type_to_statics_type(inf_ctx, ty.clone());
                constrain(left, right);
            }
            TypeDefKind::Adt(..) | TypeDefKind::Struct(..) => {}
        },
        StmtKind::Expr(expr) => {
            generate_constraints_expr(gamma, mode, expr.clone(), inf_ctx);
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            let ty_pat = TypeVar::from_node(inf_ctx, pat.id);

            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                inf_ctx,
            );

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_statics_type(inf_ctx, ty_ann.clone());
                gamma.add_polys(&ty_ann);
                generate_constraints_pat(
                    gamma,
                    Mode::Ana { expected: ty_ann },
                    pat.clone(),
                    inf_ctx,
                )
            } else {
                generate_constraints_pat(gamma, Mode::Syn, pat.clone(), inf_ctx)
            };
        }
        StmtKind::Set(lhs, rhs) => {
            let ty_lhs = TypeVar::from_node(inf_ctx, lhs.id);
            generate_constraints_expr(gamma.clone(), Mode::Syn, lhs.clone(), inf_ctx);
            let ty_rhs = TypeVar::from_node(inf_ctx, rhs.id);
            generate_constraints_expr(gamma, Mode::Syn, rhs.clone(), inf_ctx);
            constrain(ty_lhs, ty_rhs);
        }
        StmtKind::FuncDef(name, args, out_annot, body) => {
            let func_node_id = stmt.id;
            let ty_pat = TypeVar::from_node(inf_ctx, name.id);
            if add_to_gamma {
                gamma.extend(name.patkind.get_identifier_of_variable(), ty_pat.clone());
            }
            let body_gamma = gamma.new_scope();
            let ty_func = generate_constraints_func_helper(
                inf_ctx,
                func_node_id,
                body_gamma,
                args,
                out_annot,
                body,
            );

            constrain(ty_pat, ty_func);
        }
    }
}

pub(crate) fn generate_constraints_pat(
    gamma: Gamma,
    mode: Mode,
    pat: Rc<Pat>,
    inf_ctx: &mut InferenceContext,
) {
    let ty_pat = TypeVar::from_node(inf_ctx, pat.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(expected, ty_pat.clone()),
    };
    match &*pat.patkind {
        PatKind::Wildcard => (),
        PatKind::Unit => {
            constrain(ty_pat, TypeVar::make_unit(Prov::Node(pat.id)));
        }
        PatKind::Int(_) => {
            constrain(ty_pat, TypeVar::make_int(Prov::Node(pat.id)));
        }
        PatKind::Float(_) => {
            constrain(ty_pat, TypeVar::make_float(Prov::Node(pat.id)));
        }
        PatKind::Bool(_) => {
            constrain(ty_pat, TypeVar::make_bool(Prov::Node(pat.id)));
        }
        PatKind::Str(_) => {
            constrain(ty_pat, TypeVar::make_string(Prov::Node(pat.id)));
        }
        PatKind::Var(identifier) => {
            // letrec: extend context with id and type before analyzing against said type
            gamma.extend(identifier.clone(), ty_pat);
            gamma.extend_declaration(identifier.clone(), Resolution::Node(pat.id));
        }
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => TypeVar::from_node(inf_ctx, data.id),
                None => TypeVar::make_unit(Prov::VariantNoData(Box::new(Prov::Node(pat.id)))),
            };
            let mut substitution = BTreeMap::new();
            let ty_adt_instance = {
                let adt_def = inf_ctx.adt_def_of_variant(tag);

                if let Some(adt_def) = adt_def {
                    let nparams = adt_def.params.len();
                    let mut params = vec![];
                    for i in 0..nparams {
                        params.push(TypeVar::fresh(
                            inf_ctx,
                            Prov::InstantiateUdtParam(Box::new(Prov::Node(pat.id)), i as u8),
                        ));
                        substitution.insert(adt_def.params[i].clone(), params[i].clone());
                    }
                    let def_type = TypeVar::make_def_instance(
                        Prov::UdtDef(Box::new(Prov::Node(pat.id))),
                        adt_def.name,
                        params,
                    );

                    let variant_def = adt_def.variants.iter().find(|v| v.ctor == *tag).unwrap();
                    let variant_data_ty = variant_def.data.clone().subst(
                        gamma.clone(),
                        Prov::Node(pat.id),
                        &substitution,
                    );
                    constrain(ty_data.clone(), variant_data_ty);

                    def_type
                } else {
                    panic!("variant not found");
                }
            };

            constrain(ty_pat, ty_adt_instance);
            if let Some(data) = data {
                generate_constraints_pat(
                    gamma,
                    Mode::Ana { expected: ty_data },
                    data.clone(),
                    inf_ctx,
                )
            };
        }
        PatKind::Tuple(pats) => {
            let tys_elements = pats
                .iter()
                .map(|pat| TypeVar::fresh(inf_ctx, Prov::Node(pat.id)))
                .collect();
            constrain(
                ty_pat,
                TypeVar::make_tuple(tys_elements, Prov::Node(pat.id)),
            );
            for pat in pats {
                generate_constraints_pat(gamma.clone(), Mode::Syn, pat.clone(), inf_ctx)
            }
        }
    }
}

pub(crate) fn gather_definitions_stmt(
    inf_ctx: &mut InferenceContext,
    gamma: Gamma,
    stmt: Rc<Stmt>,
) {
    match &*stmt.stmtkind {
        StmtKind::InterfaceDef(ident, properties) => {
            if let Some(interface_def) = inf_ctx.interface_defs.get(ident) {
                let entry = inf_ctx
                    .multiple_interface_defs
                    .entry(ident.clone())
                    .or_default();
                entry.push(interface_def.location);
                entry.push(stmt.id);
                return;
            }
            let mut methods = vec![];
            for p in properties {
                let ty_annot =
                    ast_type_to_statics_type_interface(inf_ctx, p.ty.clone(), Some(ident));
                let node_ty = TypeVar::from_node(inf_ctx, p.id());
                constrain(node_ty.clone(), ty_annot.clone());
                methods.push(InterfaceDefMethod {
                    name: p.ident.clone(),
                    ty: node_ty.clone(),
                });
                inf_ctx
                    .method_to_interface
                    .insert(p.ident.clone(), ident.clone());
                gamma.extend(p.ident.clone(), node_ty);
            }
            inf_ctx.interface_defs.insert(
                ident.clone(),
                InterfaceDef {
                    name: ident.clone(),
                    methods,
                    location: stmt.id,
                },
            );
        }
        StmtKind::InterfaceImpl(ident, typ, stmts) => {
            let typ = ast_type_to_statics_type(inf_ctx, typ.clone());

            if typ.is_instantiated_adt() {
                inf_ctx.interface_impl_for_instantiated_adt.push(stmt.id);
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
            let impl_list = inf_ctx.interface_impls.entry(ident.clone()).or_default();
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
                if let Some(adt_def) = inf_ctx.adt_defs.get(ident) {
                    let entry = inf_ctx.multiple_udt_defs.entry(ident.clone()).or_default();
                    entry.push(adt_def.location);
                    entry.push(stmt.id);
                    return;
                }
                let mut defvariants = vec![];
                for v in variants {
                    let data = {
                        if let Some(data) = &v.data {
                            ast_type_to_statics_type(inf_ctx, data.clone())
                        } else {
                            TypeVar::make_unit(Prov::VariantNoData(Box::new(Prov::Node(v.id))))
                        }
                    };
                    defvariants.push(Variant {
                        ctor: v.ctor.clone(),
                        data,
                    });
                    inf_ctx
                        .variants_to_adt
                        .insert(v.ctor.clone(), ident.clone());
                }
                let mut defparams = vec![];
                for p in params {
                    let TypeKind::Poly(ident, _) = &*p.typekind else {
                        panic!("expected poly type for ADT def param")
                    };
                    defparams.push(ident.clone());
                }
                inf_ctx.adt_defs.insert(
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
                let ty_struct = TypeVar::from_node(inf_ctx, stmt.id);
                if let Some(struct_def) = inf_ctx.struct_defs.get(ident) {
                    let entry = inf_ctx.multiple_udt_defs.entry(ident.clone()).or_default();
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
                    let ty_annot = ast_type_to_statics_type(inf_ctx, f.ty.clone());
                    deffields.push(StructField {
                        name: f.ident.clone(),
                        ty: ty_annot.clone(),
                    });

                    let prov = Prov::StructField(f.ident.clone(), ty_struct.clone());
                    let ty_field = TypeVar::fresh(inf_ctx, prov.clone());
                    constrain(ty_field.clone(), ty_annot.clone());
                    inf_ctx.vars.insert(prov, ty_field);
                }
                inf_ctx.struct_defs.insert(
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
        StmtKind::Let(..) => {}
        StmtKind::FuncDef(name, _args, _out_annot, _body) => {
            inf_ctx
                .fun_defs
                .insert(name.patkind.get_identifier_of_variable(), stmt.clone());
            gamma.extend(
                name.patkind.get_identifier_of_variable(),
                TypeVar::from_node(inf_ctx, name.id),
            );
            gamma.extend_declaration(
                name.patkind.get_identifier_of_variable(),
                Resolution::Node(name.id),
            );
        }
        StmtKind::Set(..) => {}
    }
}

fn monomorphized_ty_to_builtin_ty(ty: TypeMonomorphized, prov_builtin: Prov) -> TypeVar {
    match ty {
        TypeMonomorphized::Unit => TypeVar::make_unit(prov_builtin),
        TypeMonomorphized::Int => TypeVar::make_int(prov_builtin),
        TypeMonomorphized::Float => TypeVar::make_float(prov_builtin),
        TypeMonomorphized::Bool => TypeVar::make_bool(prov_builtin),
        TypeMonomorphized::String => TypeVar::make_string(prov_builtin),
        TypeMonomorphized::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|e| monomorphized_ty_to_builtin_ty(e, prov_builtin.clone()))
                .collect();
            TypeVar::make_tuple(elements, prov_builtin)
        }
        TypeMonomorphized::Function(args, out) => {
            let args = args
                .into_iter()
                .map(|a| monomorphized_ty_to_builtin_ty(a, prov_builtin.clone()))
                .collect();
            let out = monomorphized_ty_to_builtin_ty(*out, prov_builtin.clone());
            TypeVar::make_func(args, out, prov_builtin.clone())
        }
        TypeMonomorphized::Adt(name, params) => {
            let params = params
                .into_iter()
                .map(|p| monomorphized_ty_to_builtin_ty(p, prov_builtin.clone()))
                .collect();
            TypeVar::make_def_instance(prov_builtin, name, params)
        }
    }
}

pub(crate) fn gather_definitions_toplevel<Effect: crate::side_effects::EffectTrait>(
    inf_ctx: &mut InferenceContext,
    gamma: Gamma, // TODO: this is dumb, don't thread gamma through, it's only used in one place in translate()
    toplevel: Rc<Toplevel>,
) {
    for eff in Effect::enumerate().iter() {
        let prov = Prov::Builtin(format!(
            "{}: {:#?}",
            eff.function_name(),
            eff.type_signature()
        ));
        let mut args = Vec::new();
        for arg in eff.type_signature().0 {
            args.push(monomorphized_ty_to_builtin_ty(arg, prov.clone()));
        }
        let typ = TypeVar::make_func(
            args,
            monomorphized_ty_to_builtin_ty(eff.type_signature().1, prov.clone()),
            prov,
        );
        gamma.extend(eff.function_name(), typ);
        gamma.extend_declaration(
            eff.function_name(),
            Resolution::Builtin(eff.function_name()),
        );
    }

    for statement in toplevel.statements.iter() {
        gather_definitions_stmt(inf_ctx, gamma.clone(), statement.clone());
    }
}

pub(crate) fn generate_constraints_toplevel(
    gamma: Gamma,
    toplevel: Rc<Toplevel>,
    inf_ctx: &mut InferenceContext,
) {
    for statement in toplevel.statements.iter() {
        generate_constraints_stmt(gamma.clone(), Mode::Syn, statement.clone(), inf_ctx, true);
    }
}

// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub(crate) fn result_of_constraint_solving(
    inf_ctx: &mut InferenceContext,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<(), String> {
    // get list of type conflicts
    let mut type_conflicts = Vec::new();
    for potential_types in inf_ctx.vars.values() {
        let type_suggestions = potential_types.0.clone_data().types; // TODO why not just check if it's solved?
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions.clone());
        }
    }

    // replace underdetermined types with unit
    if type_conflicts.is_empty() {
        for potential_types in inf_ctx.vars.values() {
            let mut data = potential_types.0.clone_data();
            let suggestions = &mut data.types;
            if suggestions.is_empty() {
                suggestions.insert(
                    TypeKey::Unit,
                    PotentialType::make_unit(Prov::UnderdeterminedCoerceToUnit),
                );
                potential_types.0.replace_data(data);
            }
        }
    }

    // look for error of multiple interface implementations for the same type
    for (ident, impls) in inf_ctx.interface_impls.iter() {
        // map from implementation type to location
        let mut impls_by_type: BTreeMap<SolvedType, Vec<NodeId>> = BTreeMap::new();
        for imp in impls.iter() {
            if let Some(impl_typ) = imp.typ.clone().solution() {
                impls_by_type
                    .entry(impl_typ)
                    .or_default()
                    .push(imp.location);
            }
        }
        for (_impl_typ, impl_locs) in impls_by_type.iter() {
            if impl_locs.len() > 1 {
                inf_ctx
                    .multiple_interface_impls
                    .insert(ident.clone(), impl_locs.clone());
            }
        }
    }

    let mut err_string = String::new();

    let mut bad_instantiations = false;
    // check for bad instantiation of polymorphic types constrained to an Interface
    for (typ, interfaces) in inf_ctx.types_constrained_to_interfaces.iter() {
        let Some(typ) = &typ.solution() else {
            continue;
        };
        // for each interface
        for interface in interfaces {
            let mut bad_instantiation: bool = true;
            let (interface, prov) = interface;
            if let SolvedType::Poly(_, interfaces2) = &typ {
                // if 'a Interface1 is constrained to [Interfaces...], ignore
                if interfaces2.contains(interface) {
                    bad_instantiation = false;
                }
            } else if let Some(impl_list) = inf_ctx.interface_impls.get(interface) {
                // find at least one implementation of interface that matches the type constrained to the interface
                for impl_ in impl_list {
                    if let Some(impl_ty) = impl_.typ.solution() {
                        if let Err((_err_monoty, _err_impl_ty)) =
                            ty_fits_impl_ty(inf_ctx, typ.clone(), impl_ty.clone())
                        {
                        } else {
                            bad_instantiation = false;
                        }
                    }
                }
            }
            if bad_instantiation {
                bad_instantiations = true;
                let _ = writeln!(
                    err_string,
                    "error: the interface '{}' is not implemented for type '{}'",
                    interface, typ
                );
                if let Some(id) = prov.get_location() {
                    let span = node_map.get(&id).unwrap().span();
                    span.display(&mut err_string, sources, "");
                }
            }
        }
    }

    let mut bad_field_access = false;
    for (typ, location) in inf_ctx.types_that_must_be_structs.iter() {
        let typ = typ.solution();
        let Some(solved) = typ else {
            continue;
        };
        if let SolvedType::UdtInstance(ident, _) = &solved {
            let struct_def = inf_ctx.struct_defs.get(ident);
            if struct_def.is_some() {
                continue;
            }
        }

        bad_field_access = true;
        let _ = writeln!(err_string, "error: type '{}' is not a struct", solved);
        let span = node_map.get(location).unwrap().span();
        span.display(&mut err_string, sources, "");
    }

    if inf_ctx.unbound_vars.is_empty()
        && inf_ctx.unbound_interfaces.is_empty()
        && type_conflicts.is_empty()
        && inf_ctx.multiple_udt_defs.is_empty()
        && inf_ctx.multiple_interface_defs.is_empty()
        && inf_ctx.multiple_interface_impls.is_empty()
        && inf_ctx.interface_impl_for_instantiated_adt.is_empty()
        && inf_ctx.interface_impl_extra_method.is_empty()
        && inf_ctx.interface_impl_missing_method.is_empty()
        && inf_ctx.annotation_needed.is_empty()
        && inf_ctx.field_not_ident.is_empty()
        && !bad_instantiations
        && !bad_field_access
    {
        for (node_id, node) in node_map.iter() {
            let ty = inf_ctx.solution_of_node(*node_id);
            let _span = node.span();
            if let Some(_ty) = ty {}
        }
        return Ok(());
    }

    if !inf_ctx.unbound_vars.is_empty() {
        err_string.push_str("You have unbound variables!\n");
        for ast_id in inf_ctx.unbound_vars.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            span.display(&mut err_string, sources, "");
        }
    }
    if !inf_ctx.unbound_interfaces.is_empty() {
        for ast_id in inf_ctx.unbound_interfaces.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "Interface being implemented is not defined\n",
            );
        }
    }
    if !inf_ctx.multiple_udt_defs.is_empty() {
        for (ident, adt_ids) in inf_ctx.multiple_udt_defs.iter() {
            let _ = writeln!(err_string, "Multiple definitions for type {}, ident", ident);
            for ast_id in adt_ids {
                let span = node_map.get(ast_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }
        }
    }
    if !inf_ctx.multiple_interface_defs.is_empty() {
        for (ident, interface_ids) in inf_ctx.multiple_interface_defs.iter() {
            let _ = writeln!(err_string, "Multiple definitions for interface {}", ident);
            for ast_id in interface_ids {
                let span = node_map.get(ast_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }
        }
    }

    if !inf_ctx.multiple_interface_impls.is_empty() {
        for (ident, impl_ids) in inf_ctx.multiple_interface_impls.iter() {
            let _ = writeln!(
                err_string,
                "Multiple implementations for interface {}",
                ident
            );
            for ast_id in impl_ids {
                let span = node_map.get(ast_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }
        }
    }

    if !inf_ctx.interface_impl_for_instantiated_adt.is_empty() {
        for ast_id in inf_ctx.interface_impl_for_instantiated_adt.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "Interface implementations for instantiated ADTs are not supported.\n",
            );
        }
    }

    if !inf_ctx.interface_impl_extra_method.is_empty() {
        for (id, impls) in inf_ctx.interface_impl_extra_method.iter() {
            let span = node_map.get(id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "this interface implementation has methods not defined in the original interface.",
            );
            for ast_id in impls {
                let span = node_map.get(ast_id).unwrap().span();
                span.display(&mut err_string, sources, "remove this method:");
            }
        }
    }

    if !inf_ctx.interface_impl_missing_method.is_empty() {
        for (id, method_names) in inf_ctx.interface_impl_missing_method.iter() {
            let span = node_map.get(id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "this interface implementation is missing methods defined in the original interface.",
            );
            // add these methods:
            err_string.push_str("Add these methods:\n");
            for method_name in method_names {
                err_string.push_str(&format!("\t- {method_name};\n"));
            }
        }
    }

    if !inf_ctx.annotation_needed.is_empty() {
        for id in inf_ctx.annotation_needed.iter() {
            let span = node_map.get(id).unwrap().span();
            span.display(&mut err_string, sources, "this needs a type annotation");
        }
    }

    if !inf_ctx.field_not_ident.is_empty() {
        for id in inf_ctx.field_not_ident.iter() {
            let span = node_map.get(id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "Need to use an identifier when accessing a field",
            );
        }
    }

    if !type_conflicts.is_empty() {
        let mut type_conflicts: Vec<Vec<PotentialType>> = type_conflicts
            .iter()
            .map(|type_suggestions| {
                let mut types_sorted: Vec<PotentialType> =
                    type_suggestions.values().cloned().collect();
                types_sorted.sort_by_key(|ty| ty.provs().borrow().len());
                types_sorted
            })
            .collect::<Vec<_>>();
        type_conflicts.sort();
        for type_conflict in &type_conflicts {
            err_string.push_str("Conflicting types: ");
            fmt_conflicting_types(type_conflict, &mut err_string).unwrap();
            writeln!(err_string).unwrap();
            for ty in type_conflict {
                err_string.push('\n');
                match &ty {
                    PotentialType::Poly(_, _, _) => {
                        err_string.push_str("Sources of generic type:\n")
                    }
                    PotentialType::UdtInstance(_, ident, params) => {
                        let _ = write!(err_string, "Sources of type {}<", ident);
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
                        let _ =
                            writeln!(err_string, "Sources of tuple with {} elements", elems.len());
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
                    Prov::Alias(_) => 5,
                    Prov::VariantNoData(_) => 7,
                    Prov::UdtDef(_) => 8,
                    Prov::InstantiateUdtParam(_, _) => 9,
                    Prov::ListElem(_) => 10,
                    Prov::BinopLeft(_) => 11,
                    Prov::BinopRight(_) => 12,
                    Prov::UnderdeterminedCoerceToUnit => 13,
                    Prov::StructField(..) => 14,
                    Prov::IndexAccess => 15,
                });
                for cause in provs_vec {
                    match cause {
                        Prov::Builtin(s) => {
                            let _ = writeln!(err_string, "The builtin function {s}");
                        }
                        Prov::Node(id) => {
                            let span = node_map.get(id).unwrap().span();
                            span.display(&mut err_string, sources, "");
                        }
                        Prov::UnderdeterminedCoerceToUnit => {
                            err_string.push_str(
                                "The type was underdetermined, so it was coerced to void.",
                            );
                        }
                        Prov::InstantiatePoly(_, ident) => {
                            let _ = writeln!(
                                err_string,
                                "The instantiation of polymorphic type {ident}"
                            );
                        }
                        Prov::FuncArg(prov, n) => {
                            match prov.as_ref() {
                                Prov::Builtin(s) => {
                                    let n = n + 1; // readability
                                    let _ = writeln!(
                                        err_string,
                                        "--> The #{n} argument of function '{s}'"
                                    );
                                }
                                Prov::Node(id) => {
                                    let span = node_map.get(id).unwrap().span();
                                    span.display(
                                        &mut err_string,
                                        sources,
                                        &format!("The #{n} argument of this function"),
                                    );
                                }
                                _ => unreachable!(),
                            }
                        }
                        Prov::FuncOut(prov) => match prov.as_ref() {
                            Prov::Builtin(s) => {
                                let _ = writeln!(
                                    err_string,
                                    "
                                    --> The output of the builtin function '{s}'"
                                );
                            }
                            Prov::Node(id) => {
                                let span = node_map.get(id).unwrap().span();
                                span.display(
                                    &mut err_string,
                                    sources,
                                    "The output of this function",
                                );
                            }
                            _ => unreachable!(),
                        },
                        Prov::BinopLeft(inner) => {
                            err_string.push_str("The left operand of operator\n");
                            if let Prov::Node(id) = **inner {
                                let span = node_map.get(&id).unwrap().span();
                                span.display(&mut err_string, sources, "");
                            }
                        }
                        Prov::BinopRight(inner) => {
                            err_string.push_str("The left operand of this operator\n");
                            if let Prov::Node(id) = **inner {
                                let span = node_map.get(&id).unwrap().span();
                                span.display(&mut err_string, sources, "");
                            }
                        }
                        Prov::ListElem(_) => {
                            err_string.push_str("The element of some list");
                        }
                        Prov::Alias(ident) => {
                            let _ = writeln!(err_string, "The type alias {ident}");
                        }
                        Prov::UdtDef(_prov) => {
                            err_string.push_str("Some ADT definition");
                        }
                        Prov::InstantiateUdtParam(_, _) => {
                            err_string.push_str("Some instance of an Adt's variant");
                        }
                        Prov::VariantNoData(_prov) => {
                            err_string.push_str("The data of some ADT variant");
                        }
                        Prov::StructField(field, ty) => {
                            let _ = writeln!(err_string, "The field {field} of the struct {ty}");
                        }
                        Prov::IndexAccess => {
                            let _ = writeln!(err_string, "Index for array access");
                        }
                    }
                }
            }
            writeln!(err_string).unwrap();
        }
    }

    Err(err_string)
}

pub(crate) fn result_of_additional_analysis(
    inf_ctx: &mut InferenceContext,
    toplevels: &[Rc<Toplevel>],
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<(), String> {
    for toplevel in toplevels {
        check_pattern_exhaustiveness_toplevel(inf_ctx, toplevel);
    }

    if inf_ctx.nonexhaustive_matches.is_empty() && inf_ctx.redundant_matches.is_empty() {
        return Ok(());
    }

    let mut err_string = String::new();

    err_string.push_str("Pattern matching errors:\n");

    for (pat, missing_pattern_suggestions) in inf_ctx.nonexhaustive_matches.iter() {
        let span = node_map.get(pat).unwrap().span();
        span.display(
            &mut err_string,
            sources,
            "This match expression doesn't cover every possibility:\n",
        );
        err_string.push_str("\nThe following cases are missing:\n");
        for pat in missing_pattern_suggestions {
            let _ = writeln!(err_string, "\t`{pat}`\n");
        }
    }

    for (match_expr, redundant_pattern_suggestions) in inf_ctx.redundant_matches.iter() {
        let span = node_map.get(match_expr).unwrap().span();
        span.display(
            &mut err_string,
            sources,
            "This match expression has redundant cases:\n",
        );
        err_string.push_str("\nTry removing these cases\n");
        for pat in redundant_pattern_suggestions {
            let span = node_map.get(pat).unwrap().span();
            span.display(&mut err_string, sources, "");
        }
    }

    Err(err_string)
}

fn check_pattern_exhaustiveness_toplevel(inf_ctx: &mut InferenceContext, toplevel: &Toplevel) {
    for statement in toplevel.statements.iter() {
        check_pattern_exhaustiveness_stmt(inf_ctx, statement);
    }
}

fn check_pattern_exhaustiveness_stmt(inf_ctx: &mut InferenceContext, stmt: &Stmt) {
    match &*stmt.stmtkind {
        StmtKind::InterfaceDef(..) => {}
        StmtKind::TypeDef(..) => {}
        StmtKind::InterfaceImpl(_, _, stmts) => {
            for stmt in stmts {
                check_pattern_exhaustiveness_stmt(inf_ctx, stmt);
            }
        }
        StmtKind::Set(_, expr) => {
            check_pattern_exhaustiveness_expr(inf_ctx, expr);
        }
        StmtKind::Let(_, _, expr) => {
            check_pattern_exhaustiveness_expr(inf_ctx, expr);
        }
        StmtKind::FuncDef(_, _, _, body) => {
            check_pattern_exhaustiveness_expr(inf_ctx, body);
        }
        StmtKind::Expr(expr) => {
            check_pattern_exhaustiveness_expr(inf_ctx, expr);
        }
    }
}

fn check_pattern_exhaustiveness_expr(inf_ctx: &mut InferenceContext, expr: &Expr) {
    match &*expr.exprkind {
        ExprKind::Match(..) => match_expr_exhaustive_check(inf_ctx, expr),

        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::Var { .. } => {}
        ExprKind::List(exprs) => {
            for expr in exprs {
                check_pattern_exhaustiveness_expr(inf_ctx, expr);
            }
        }
        ExprKind::Array(exprs) => {
            for expr in exprs {
                check_pattern_exhaustiveness_expr(inf_ctx, expr);
            }
        }
        ExprKind::BinOp(left, _op, right) => {
            check_pattern_exhaustiveness_expr(inf_ctx, left);
            check_pattern_exhaustiveness_expr(inf_ctx, right);
        }
        ExprKind::Block(statements) => {
            for statement in statements {
                check_pattern_exhaustiveness_stmt(inf_ctx, statement);
            }
        }
        ExprKind::If(e1, e2, e3) => {
            check_pattern_exhaustiveness_expr(inf_ctx, e1);
            check_pattern_exhaustiveness_expr(inf_ctx, e2);
            if let Some(e3) = e3 {
                check_pattern_exhaustiveness_expr(inf_ctx, e3);
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            check_pattern_exhaustiveness_expr(inf_ctx, cond);
            check_pattern_exhaustiveness_expr(inf_ctx, expr);
        }
        ExprKind::Func(_args, _out_annot, body) => {
            check_pattern_exhaustiveness_expr(inf_ctx, body);
        }
        ExprKind::FuncAp(func, args) => {
            check_pattern_exhaustiveness_expr(inf_ctx, func);
            for arg in args {
                check_pattern_exhaustiveness_expr(inf_ctx, arg);
            }
        }
        ExprKind::Tuple(exprs) => {
            for expr in exprs {
                check_pattern_exhaustiveness_expr(inf_ctx, expr);
            }
        }
        ExprKind::FieldAccess(expr, _) => {
            check_pattern_exhaustiveness_expr(inf_ctx, expr);
        }
        ExprKind::IndexAccess(expr, index) => {
            check_pattern_exhaustiveness_expr(inf_ctx, expr);
            check_pattern_exhaustiveness_expr(inf_ctx, index);
        }
    }
}

pub(crate) fn ty_fits_impl_ty(
    ctx: &InferenceContext,
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
        (SolvedType::UdtInstance(ident1, tys1), SolvedType::UdtInstance(ident2, tys2)) => {
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
    inf_ctx: &InferenceContext,
    typ: SolvedType,
    interfaces: BTreeSet<Symbol>,
) -> bool {
    for interface in interfaces {
        if let SolvedType::Poly(_, interfaces2) = &typ {
            // if 'a Interface1 is constrained to [Interfaces...], ignore
            if interfaces2.contains(&interface) {
                return true;
            }
        }
        if let Some(impl_list) = inf_ctx.interface_impls.get(&interface) {
            // find at least one implementation of interface that matches the type constrained to the interface
            for impl_ in impl_list {
                if let Some(impl_ty) = impl_.typ.solution() {
                    if ty_fits_impl_ty(inf_ctx, typ.clone(), impl_ty).is_ok() {
                        return true;
                    }
                }
            }
        }
    }
    false
}

// Exhaustiveness and usefulness analysis for pattern matching
// uses same algorithm as Rust compiler: https://doc.rust-lang.org/nightly/nightly-rustc/rustc_pattern_analysis/usefulness/index.html
#[derive(Debug, Clone)]
struct Matrix {
    rows: Vec<MatrixRow>,
    types: Vec<SolvedType>,
}

impl Matrix {
    fn new(inf_ctx: &InferenceContext, scrutinee_ty: SolvedType, arms: &[MatchArm]) -> Self {
        let types = vec![scrutinee_ty.clone()];
        let mut rows = Vec::new();
        for (dummy, arm) in arms.iter().enumerate() {
            let pats = vec![DeconstructedPat::from_ast_pat(inf_ctx, arm.pat.clone())];
            rows.push(MatrixRow {
                pats,
                parent_row: dummy,
                useful: false,
            });
        }
        Self { rows, types }
    }

    fn head_column(&self) -> Vec<DeconstructedPat> {
        if self.rows.is_empty() {
            return vec![];
        }
        self.rows.iter().map(|row| row.head()).collect()
    }

    fn specialize(
        &self,
        ctor: &Constructor,
        ctor_arity: usize,
        inf_ctx: &InferenceContext,
    ) -> Matrix {
        let mut new_types = Vec::new();
        match ctor {
            Constructor::Int(..)
            | Constructor::Float(..)
            | Constructor::String(..)
            | Constructor::Bool(..)
            | Constructor::Wildcard(..) => {}
            Constructor::Product => match &self.types[0] {
                SolvedType::Tuple(tys) => {
                    new_types.extend(tys.clone());
                }
                SolvedType::Unit => {}
                _ => panic!("unexpected type for product constructor"),
            },
            Constructor::Variant(ident) => {
                let adt = inf_ctx.adt_def_of_variant(ident).unwrap();
                let variant = adt.variants.iter().find(|v| v.ctor == *ident).unwrap();
                let data_ty = variant.data.solution().unwrap();
                match data_ty {
                    SolvedType::Unit => {}
                    SolvedType::Bool
                    | SolvedType::Int
                    | SolvedType::String
                    | SolvedType::Float
                    | SolvedType::Function(..)
                    | SolvedType::Tuple(_)
                    | SolvedType::UdtInstance(..) => new_types.push(data_ty),
                    _ => panic!("unexpected type"),
                }
            }
        }

        new_types.extend(self.types[1..].iter().cloned());

        let mut new_matrix = Matrix {
            rows: vec![],
            types: new_types,
        };
        for (i, row) in self.rows.iter().enumerate() {
            if row.pats.is_empty() {
                panic!("no pats in row");
            }
            if ctor.is_covered_by(&row.head().ctor) {
                let new_row = row.pop_head(ctor, ctor_arity, i, inf_ctx);
                new_matrix.rows.push(new_row);
            }
        }
        new_matrix
    }

    fn unspecialize(&mut self, specialized: Self) {
        for child_row in specialized.rows.iter() {
            let parent_row = &mut self.rows[child_row.parent_row];
            parent_row.useful |= child_row.useful;
        }
    }
}

impl fmt::Display for Matrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        for row in self.rows.iter() {
            if row.pats.is_empty() {
                write!(f, "()")?;
            }
            for (i, pat) in row.pats.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", pat)?;
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
struct MatrixRow {
    pats: Vec<DeconstructedPat>,
    parent_row: usize,
    useful: bool,
}

impl MatrixRow {
    fn head(&self) -> DeconstructedPat {
        match self.pats.first() {
            Some(p) => p.clone(),
            None => panic!(),
        }
    }

    fn pop_head(
        &self,
        other_ctor: &Constructor,
        arity: usize,
        parent_row: usize,
        inf_ctx: &InferenceContext,
    ) -> MatrixRow {
        if self.pats.is_empty() {
            panic!("no pats in row");
        }

        let head_pat = self.head();

        let mut new_pats = head_pat.specialize(other_ctor, arity, inf_ctx);

        new_pats.extend_from_slice(&self.pats[1..]);
        MatrixRow {
            pats: new_pats,
            parent_row,
            useful: false,
        }
    }
}

#[derive(Debug, Clone)]
pub(crate) struct DeconstructedPat {
    ctor: Constructor,
    fields: Vec<DeconstructedPat>,
    ty: SolvedType,
}

impl DeconstructedPat {
    fn from_ast_pat(inf_ctx: &InferenceContext, pat: Rc<Pat>) -> Self {
        let ty = inf_ctx.solution_of_node(pat.id).unwrap();
        let mut fields = vec![];
        let ctor = match &*pat.patkind {
            PatKind::Wildcard => Constructor::Wildcard(WildcardReason::UserCreated),
            PatKind::Var(_ident) => Constructor::Wildcard(WildcardReason::VarPat),
            PatKind::Bool(b) => Constructor::Bool(*b),
            PatKind::Int(i) => Constructor::Int(*i),
            PatKind::Float(f) => Constructor::Float(*f),
            PatKind::Str(s) => Constructor::String(s.clone()),
            PatKind::Unit => Constructor::Product,
            PatKind::Tuple(pats) => {
                fields = pats
                    .iter()
                    .map(|pat| DeconstructedPat::from_ast_pat(inf_ctx, pat.clone()))
                    .collect();
                Constructor::Product
            }
            PatKind::Variant(ident, pats) => {
                fields = pats
                    .iter()
                    .map(|pat| DeconstructedPat::from_ast_pat(inf_ctx, pat.clone()))
                    .collect();
                Constructor::Variant(ident.clone())
            }
        };
        Self { ctor, fields, ty }
    }

    fn specialize(
        &self,
        other_ctor: &Constructor,
        arity: usize,
        inf_ctx: &InferenceContext,
    ) -> Vec<DeconstructedPat> {
        match &self.ctor {
            Constructor::Wildcard(_) => {
                let field_tys = self.field_tys(other_ctor, inf_ctx);
                (0..arity)
                    .map(|i| DeconstructedPat {
                        ctor: Constructor::Wildcard(WildcardReason::MatrixSpecialization),
                        fields: vec![],
                        ty: field_tys[i].clone(),
                    })
                    .collect()
            }
            _ => self.fields.clone(),
        }
    }

    fn field_tys(&self, ctor: &Constructor, inf_ctx: &InferenceContext) -> Vec<SolvedType> {
        match &self.ty {
            SolvedType::Int
            | SolvedType::Float
            | SolvedType::String
            | SolvedType::Bool
            | SolvedType::Unit
            | SolvedType::Poly(..)
            | SolvedType::Function(..) => vec![],
            SolvedType::Tuple(tys) => tys.clone(),
            SolvedType::UdtInstance(_, _) => match ctor {
                Constructor::Variant(ident) => {
                    let adt = inf_ctx.adt_def_of_variant(ident).unwrap();
                    let variant = adt.variants.iter().find(|v| v.ctor == *ident).unwrap();
                    if !matches!(&variant.data.solution().unwrap(), SolvedType::Unit) {
                        vec![variant.data.solution().unwrap().clone()]
                    } else {
                        vec![]
                    }
                }
                Constructor::Wildcard(_) => {
                    vec![]
                }
                _ => panic!("unexpected constructor"),
            },
        }
    }

    fn missing_from_ctor(ctor: &Constructor, ty: SolvedType) -> Self {
        let fields = match ty.clone() {
            SolvedType::Tuple(tys) | SolvedType::UdtInstance(_, tys) => tys
                .iter()
                .map(|ty| DeconstructedPat {
                    ctor: Constructor::Wildcard(WildcardReason::NonExhaustive),
                    fields: vec![],
                    ty: ty.clone(),
                })
                .collect(),
            _ => vec![],
        };
        Self {
            ctor: ctor.clone(),
            fields,
            ty,
        }
    }
}

impl fmt::Display for DeconstructedPat {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.ctor {
            Constructor::Wildcard(_) => write!(f, "_"),
            Constructor::Bool(b) => write!(f, "{}", b),
            Constructor::Int(i) => write!(f, "{}", i),
            Constructor::Float(fl) => write!(f, "{}", fl),
            Constructor::String(s) => write!(f, "{}", s),
            Constructor::Product => {
                write!(f, "(")?;
                for (i, field) in self.fields.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", field)?;
                }
                write!(f, ")")
            }
            Constructor::Variant(ident) => {
                write!(f, "{}", ident)?;
                if !self.fields.is_empty() {
                    write!(f, " of ")?;
                    for (i, field) in self.fields.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", field)?;
                    }
                }
                Ok(())
            }
        }
    }
}

#[derive(Debug, Clone)]
enum Constructor {
    Wildcard(WildcardReason), // user-created wildcard pattern
    Bool(bool),
    Int(i64),
    Float(f32),
    String(String),
    Product, // tuples, including unit
    Variant(Symbol),
}

impl Constructor {
    fn is_covered_by(&self, other: &Constructor) -> bool {
        match (self, other) {
            (_, Constructor::Wildcard(_)) => true,
            (Constructor::Wildcard(_), _) => false,

            (Constructor::Bool(b1), Constructor::Bool(b2)) => b1 == b2,
            (Constructor::Variant(v1), Constructor::Variant(v2)) => v1 == v2,
            (Constructor::Int(i1), Constructor::Int(i2)) => i1 == i2,
            (Constructor::Float(f1), Constructor::Float(f2)) => f1 == f2,
            (Constructor::String(s1), Constructor::String(s2)) => s1 == s2,
            (Constructor::Product, Constructor::Product) => true,
            _ => panic!("comparing incompatible constructors"),
        }
    }

    fn as_bool(&self) -> Option<bool> {
        match self {
            Constructor::Bool(b) => Some(*b),
            _ => None,
        }
    }

    fn as_variant_identifier(&self) -> Option<Symbol> {
        match self {
            Constructor::Variant(i) => Some(i.clone()),
            _ => None,
        }
    }

    fn arity(&self, matrix_tys: &[SolvedType], inf_ctx: &InferenceContext) -> usize {
        match self {
            Constructor::Bool(..)
            | Constructor::Int(..)
            | Constructor::String(..)
            | Constructor::Float(..)
            | Constructor::Wildcard(..) => 0,
            Constructor::Product => match &matrix_tys[0] {
                SolvedType::Tuple(tys) => tys.len(),
                SolvedType::Unit => 0,
                _ => panic!("unexpected type for product constructor: {}", matrix_tys[0]),
            },
            Constructor::Variant(ident) => {
                let adt = inf_ctx.adt_def_of_variant(ident).unwrap();
                let variant = adt.variants.iter().find(|v| v.ctor == *ident).unwrap();
                if !matches!(&variant.data.solution().unwrap(), SolvedType::Unit) {
                    1
                } else {
                    0
                }
            }
        }
    }

    fn is_wildcard_nonexhaustive(&self) -> bool {
        matches!(self, Constructor::Wildcard(WildcardReason::NonExhaustive))
    }
}

#[derive(Debug, Clone)]
enum WildcardReason {
    UserCreated,          // a wildcard typed by the user
    VarPat, // a variable pattern created by the user, which similar to wildcard, matches anything
    NonExhaustive, // wildcards introduced by algorithm when user did not cover all constructors
    MatrixSpecialization, // wildcards introduced by algorithm during matrix specialization, which are potentially expanded from _ to (_, _, _) etc.
}

#[derive(Debug, Clone)]
struct WitnessMatrix {
    rows: Vec<Vec<DeconstructedPat>>,
}

impl WitnessMatrix {
    fn empty() -> Self {
        Self { rows: vec![] }
    }

    fn unit_witness() -> Self {
        Self { rows: vec![vec![]] }
    }

    fn extend(&mut self, other: &Self) {
        self.rows.extend_from_slice(&other.rows);
    }

    fn push_pattern(&mut self, pat: DeconstructedPat) {
        for witness in self.rows.iter_mut() {
            witness.push(pat.clone());
        }
    }

    fn apply_constructor(&mut self, ctor: &Constructor, arity: usize, head_ty: &SolvedType) {
        for witness in self.rows.iter_mut() {
            let len = witness.len();
            let fields: Vec<DeconstructedPat> = witness.drain((len - arity)..).rev().collect();
            let first_pat = DeconstructedPat {
                ctor: ctor.clone(),
                fields,
                ty: head_ty.clone(),
            };

            witness.push(first_pat);
        }
    }

    fn apply_missing_constructors(&mut self, missing_ctors: &[Constructor], head_ty: &SolvedType) {
        if missing_ctors.is_empty() {
            return;
        }

        let mut ret = Self::empty();
        for ctor in missing_ctors.iter() {
            let mut witness_matrix = self.clone();
            let missing_pat = DeconstructedPat::missing_from_ctor(ctor, head_ty.clone());
            witness_matrix.push_pattern(missing_pat);
            ret.extend(&witness_matrix);
        }
        *self = ret;
    }

    fn first_column(&self) -> Vec<DeconstructedPat> {
        self.rows.iter().map(|row| row[0].clone()).collect()
    }
}

impl fmt::Display for WitnessMatrix {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        writeln!(f)?;
        for row in self.rows.iter() {
            if row.len() > 1 {
                write!(f, "(")?;
            }
            for (i, pat) in row.iter().enumerate() {
                if i != 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", pat)?;
            }
            if row.len() > 1 {
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

#[derive(Debug, Clone)]
enum ConstructorSet {
    Bool,
    AdtVariants(Vec<Symbol>),
    Product,    // tuples, including unit
    Unlistable, // int, float, string
}

#[derive(Debug, Clone)]
struct SplitConstructorSet {
    pub(crate) present_ctors: Vec<Constructor>,
    pub(crate) missing_ctors: Vec<Constructor>,
}

impl ConstructorSet {
    fn split(&self, head_ctors: &[Constructor]) -> SplitConstructorSet {
        let mut present_ctors = Vec::new();
        let mut missing_ctors = Vec::new();
        // Constructors in `head_ctors`, except wildcards and opaques.
        let mut seen: Vec<Constructor> = Vec::new();
        let mut wildcard_seen = false;
        for ctor in head_ctors.iter().cloned() {
            if let Constructor::Wildcard(_) = &ctor {
                wildcard_seen = true;
            }
            seen.push(ctor)
        }

        match self {
            ConstructorSet::Product => {
                if !seen.is_empty() {
                    present_ctors.push(Constructor::Product);
                } else {
                    missing_ctors.push(Constructor::Product);
                }
            }
            ConstructorSet::AdtVariants(adt_variants) => {
                let mut missing_set: HashSet<Symbol> = adt_variants.iter().cloned().collect();
                for identifier in seen.iter().filter_map(|ctor| ctor.as_variant_identifier()) {
                    if missing_set.remove(&identifier) {
                        present_ctors.push(Constructor::Variant(identifier.clone()));
                    }
                }
                for identifier in missing_set {
                    missing_ctors.push(Constructor::Variant(identifier));
                }
            }
            ConstructorSet::Bool => {
                let mut seen_false = false;
                let mut seen_true = false;
                for b in seen.iter().filter_map(|ctor| ctor.as_bool()) {
                    if b {
                        seen_true = true;
                    } else {
                        seen_false = true;
                    }
                }
                if seen_false {
                    present_ctors.push(Constructor::Bool(false));
                } else {
                    missing_ctors.push(Constructor::Bool(false));
                }
                if seen_true {
                    present_ctors.push(Constructor::Bool(true));
                } else {
                    missing_ctors.push(Constructor::Bool(true));
                }
            }
            ConstructorSet::Unlistable => {
                present_ctors.extend(seen);
                if !wildcard_seen {
                    missing_ctors.push(Constructor::Wildcard(WildcardReason::NonExhaustive));
                }
            }
        }

        SplitConstructorSet {
            present_ctors,
            missing_ctors,
        }
    }
}

// identify missing and extra constructors in patterns
fn match_expr_exhaustive_check(inf_ctx: &mut InferenceContext, expr: &Expr) {
    let ExprKind::Match(scrutiny, arms) = &*expr.exprkind else {
        panic!()
    };

    let scrutinee_ty = inf_ctx.solution_of_node(scrutiny.id);
    let Some(scrutinee_ty) = scrutinee_ty else {
        return;
    };

    let mut matrix = Matrix::new(inf_ctx, scrutinee_ty, arms);

    let witness_matrix = compute_exhaustiveness_and_usefulness(inf_ctx, &mut matrix);

    let witness_patterns = witness_matrix.first_column();
    if !witness_patterns.is_empty() {
        inf_ctx
            .nonexhaustive_matches
            .insert(expr.id, witness_patterns);
    }

    let mut useless_indices = HashSet::new();
    for (i, row) in matrix.rows.iter().enumerate() {
        if !row.useful {
            useless_indices.insert(i);
        }
    }
    let mut redundant_arms = Vec::new();
    redundant_arms.extend(arms.iter().enumerate().filter_map(|(i, arm)| {
        if useless_indices.contains(&i) {
            Some(arm.pat.id)
        } else {
            None
        }
    }));
    if !redundant_arms.is_empty() {
        inf_ctx.redundant_matches.insert(expr.id, redundant_arms);
    }
}

// here's where the actual match usefulness algorithm goes
fn compute_exhaustiveness_and_usefulness(
    inf_ctx: &InferenceContext,
    matrix: &mut Matrix,
) -> WitnessMatrix {
    // base case
    let Some(head_ty) = matrix.types.first().cloned() else {
        // we are morally pattern matching on ()
        let mut useful = true;
        // only the first row is useful
        for row in matrix.rows.iter_mut() {
            row.useful = useful;
            useful = false;
        }
        let no_useful_rows = useful;
        return if no_useful_rows {
            // match was not exhaustive (there were no rows)

            WitnessMatrix::unit_witness()
        } else {
            // match was exhaustive

            WitnessMatrix::empty()
        };
    };

    let mut ret_witnesses = WitnessMatrix::empty();

    let head_ctors: Vec<Constructor> = matrix
        .head_column()
        .iter()
        .cloned()
        .map(|pat| pat.ctor)
        .collect();

    let ctors_for_ty = ctors_for_ty(inf_ctx, &head_ty);
    let SplitConstructorSet {
        mut present_ctors,
        missing_ctors,
    } = ctors_for_ty.split(&head_ctors);

    // special constructor representing cases not listed by user
    if !missing_ctors.is_empty() {
        present_ctors.push(Constructor::Wildcard(WildcardReason::NonExhaustive));
    }

    for ctor in present_ctors {
        let ctor_arity = ctor.arity(&matrix.types, inf_ctx);

        let mut specialized_matrix = matrix.specialize(&ctor, ctor_arity, inf_ctx);

        let mut witnesses = compute_exhaustiveness_and_usefulness(inf_ctx, &mut specialized_matrix);

        if ctor.is_wildcard_nonexhaustive() {
            // special constructor representing cases not listed by user
            witnesses.apply_missing_constructors(&missing_ctors, &head_ty);
        } else {
            witnesses.apply_constructor(&ctor, ctor_arity, &head_ty);
        }

        ret_witnesses.extend(&witnesses);

        matrix.unspecialize(specialized_matrix);
    }

    ret_witnesses
}

fn ctors_for_ty(inf_ctx: &InferenceContext, ty: &SolvedType) -> ConstructorSet {
    match ty {
        SolvedType::Bool => ConstructorSet::Bool,
        SolvedType::UdtInstance(ident, _) => {
            let variants = inf_ctx.variants_of_adt(ident);
            ConstructorSet::AdtVariants(variants)
        }
        SolvedType::Tuple(..) => ConstructorSet::Product,
        SolvedType::Unit => ConstructorSet::Product,
        SolvedType::Int | SolvedType::Float | SolvedType::String | SolvedType::Function(..) => {
            ConstructorSet::Unlistable
        }
        SolvedType::Poly(..) => ConstructorSet::Unlistable,
    }
}

impl fmt::Display for PotentialType {
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
                        write!(f, "{}", interface)?;
                    }
                }
                Ok(())
            }
            PotentialType::UdtInstance(_, ident, params) => {
                if !params.is_empty() {
                    write!(f, "{}<", ident)?;
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", ident)
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

impl fmt::Display for SolvedType {
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
                        write!(f, "{}", interface)?;
                    }
                }
                Ok(())
            }
            SolvedType::UdtInstance(ident, params) => {
                if !params.is_empty() {
                    write!(f, "{}<", ident)?;
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{}", param)?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", ident)
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

impl fmt::Display for Variant {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} {}", self.ctor, self.data)
    }
}

fn fmt_conflicting_types(types: &[PotentialType], f: &mut dyn Write) -> fmt::Result {
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
