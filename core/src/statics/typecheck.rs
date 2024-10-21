use crate::ast::BinOpcode;
use crate::ast::{
    ArgAnnotated, AstType, Expr, ExprKind, Identifier, Node, NodeId, NodeMap, Pat, PatKind,
    Sources, Stmt, StmtKind, Toplevel, TypeDefKind, TypeKind,
};
use crate::builtin::Builtin;
use crate::environment::Environment;
use core::panic;
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt::{self, Write};
use std::rc::Rc;

use super::{Resolution, StaticsContext};

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

    fn solution(&self) -> Option<SolvedType> {
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
    Poly(Provs, Identifier, Vec<Identifier>), // type name, then list of Interfaces it must match
    Unit(Provs),
    Int(Provs),
    Float(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<TypeVar>, TypeVar),
    Tuple(Provs, Vec<TypeVar>),
    UdtInstance(Provs, Identifier, Vec<TypeVar>), // TODO: instead of Symbol, use a node_id of the declaration. Types should be able to share the same name
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SolvedType {
    Poly(Identifier, Vec<Identifier>), // type name, then list of Interfaces it must match
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<SolvedType>, Box<SolvedType>),
    Tuple(Vec<SolvedType>),
    UdtInstance(Identifier, Vec<SolvedType>),
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
            Self::UdtInstance(ident, params) => {
                let mut params2: Vec<Monotype> = vec![];
                for param in params {
                    if let Some(param) = param.monotype() {
                        params2.push(param);
                    } else {
                        return None;
                    }
                }
                Some(Monotype::Enum(ident.clone(), params2))
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
            Self::UdtInstance(_, tys) => tys.iter().any(|ty| ty.is_overloaded()),
        }
    }
}

// This is the fully instantiated AKA monomorphized type of an interface's implementation
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Monotype {
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<Monotype>, Box<Monotype>),
    Tuple(Vec<Monotype>),
    Enum(Identifier, Vec<Monotype>),
}

impl fmt::Display for Monotype {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Monotype::Enum(ident, params) => {
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

// If two types don't share the same key, they must be in conflict
// (If two types share the same key, they may or may not be in conflict)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum TypeKey {
    Poly,                  // TODO: why isn't the Identifier included here?
    TyApp(Identifier, u8), // u8 represents the number of type params
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(u8), // u8 represents the number of arguments
    Tuple(u8),    // u8 represents the number of elements
}

// Provenances are used to:
// (1) give the *unique* identity of an unknown type variable (UnifVar) in the SolutionMap
// (2) track the origins (plural!) of a type's constraints for error reporting
// TODO: Does Prov really need to be that deeply nested? Will there really be FuncArg -> InstantiatedPoly -> BinopLeft -> Node? Or can we simplify here?
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Prov {
    Node(NodeId),     // the type of an expression or statement located at NodeId
    Builtin(Builtin), // a builtin function or constant, which doesn't exist in the AST
    Effect(u16),
    UnderdeterminedCoerceToUnit,

    Alias(Identifier), // TODO FIXME: Store a NodeId/resolution instead of a Symbol
    UdtDef(Box<Prov>),

    InstantiateUdtParam(Box<Prov>, u8),
    InstantiatePoly(Box<Prov>, Identifier),
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
    BinopLeft(Box<Prov>),
    BinopRight(Box<Prov>),
    ListElem(Box<Prov>),
    StructField(Identifier, NodeId),
    IndexAccess,
    VariantNoData(Box<Prov>), // the type of the data of a variant with no data, always Unit.
}

impl Prov {
    // TODO: Can we make this not Optional? Only reason it would fail is if the last prov in the chain is a builtin
    // TODO: remove Builtin prov for this reason, defeats the purpose. Builtins should be declared in the PRELUDE, and that declaration will be the Prov.
    fn get_location(&self) -> Option<NodeId> {
        match self {
            Prov::Node(id) => Some(*id),
            Prov::Builtin(_) => None,
            Prov::Effect(_) => None,
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
            PotentialType::UdtInstance(_, ident, params) => {
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

    fn provs(&self) -> &Provs {
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

    fn make_unit(prov: Prov) -> PotentialType {
        PotentialType::Unit(provs_singleton(prov))
    }

    fn make_int(prov: Prov) -> PotentialType {
        PotentialType::Int(provs_singleton(prov))
    }

    fn make_float(prov: Prov) -> PotentialType {
        PotentialType::Float(provs_singleton(prov))
    }

    fn make_bool(prov: Prov) -> PotentialType {
        PotentialType::Bool(provs_singleton(prov))
    }

    fn make_string(prov: Prov) -> PotentialType {
        PotentialType::String(provs_singleton(prov))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, prov: Prov) -> PotentialType {
        PotentialType::Function(provs_singleton(prov), args, out)
    }

    fn make_tuple(elems: Vec<TypeVar>, prov: Prov) -> PotentialType {
        PotentialType::Tuple(provs_singleton(prov), elems)
    }

    fn make_poly(prov: Prov, ident: String, interfaces: Vec<String>) -> PotentialType {
        PotentialType::Poly(provs_singleton(prov), ident, interfaces)
    }

    fn make_poly_constrained(prov: Prov, ident: String, interface_ident: String) -> PotentialType {
        PotentialType::Poly(provs_singleton(prov), ident, vec![interface_ident])
    }

    fn make_def_instance(prov: Prov, ident: String, params: Vec<TypeVar>) -> PotentialType {
        PotentialType::UdtInstance(provs_singleton(prov), ident, params)
    }
}

impl TypeVar {
    // Creates a clone of a Type with polymorphic variables not in scope with fresh unification variables
    fn instantiate(self, gamma: Gamma, ctx: &mut StaticsContext, prov: Prov) -> TypeVar {
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
                        ctx,
                        Prov::InstantiatePoly(Box::new(prov.clone()), ident.clone()),
                    );
                    let mut extension = Vec::new();
                    for i in interfaces {
                        extension.push((i.clone(), prov.clone()));
                    }
                    ctx.types_constrained_to_interfaces
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
                    .map(|ty| ty.instantiate(gamma.clone(), ctx, prov.clone()))
                    .collect();
                PotentialType::UdtInstance(provs, ident, params)
            }
            PotentialType::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), ctx, prov.clone()))
                    .collect();
                let out = out.instantiate(gamma.clone(), ctx, prov.clone());
                PotentialType::Function(provs, args, out)
            }
            PotentialType::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), ctx, prov.clone()))
                    .collect();
                PotentialType::Tuple(provs, elems)
            }
        };
        let mut types = BTreeMap::new();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData { types };
        let tvar = TypeVar(UnionFindNode::new(data_instantiated));
        ctx.vars.insert(prov, tvar.clone());
        tvar
    }

    // Creates a *new* Type with polymorphic variabels replaced by subtitutions
    fn subst(
        self,
        gamma: Gamma,
        prov: Prov,
        substitution: &BTreeMap<Identifier, TypeVar>,
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

    pub(crate) fn from_node(ctx: &mut StaticsContext, id: NodeId) -> TypeVar {
        let prov = Prov::Node(id);
        Self::fresh(ctx, prov)
    }

    pub(crate) fn fresh(ctx: &mut StaticsContext, prov: Prov) -> TypeVar {
        match ctx.vars.get(&prov) {
            Some(ty) => ty.clone(),
            None => {
                let ty = TypeVar(UnionFindNode::new(TypeVarData::new()));
                ctx.vars.insert(prov, ty.clone());
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

    fn make_int(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_int(prov))
    }

    fn make_float(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_float(prov))
    }

    fn make_bool(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_bool(prov))
    }

    fn make_string(prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_string(prov))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_func(args, out, prov))
    }

    fn make_tuple(elems: Vec<TypeVar>, prov: Prov) -> TypeVar {
        Self::orphan(PotentialType::make_tuple(elems, prov))
    }

    fn make_poly(prov: Prov, ident: String, interfaces: Vec<String>) -> TypeVar {
        Self::orphan(PotentialType::make_poly(prov, ident, interfaces))
    }

    fn make_poly_constrained(prov: Prov, ident: String, interface_ident: String) -> TypeVar {
        Self::orphan(PotentialType::make_poly_constrained(
            prov,
            ident,
            interface_ident,
        ))
    }

    fn make_def_instance(prov: Prov, ident: String, params: Vec<TypeVar>) -> TypeVar {
        Self::orphan(PotentialType::make_def_instance(prov, ident, params))
    }

    // return true if the type is an enumt with at least one parameter instantiated
    // this is used to see if an implementation of an interface is for an instantiated enumt, which is not allowed
    // example: implement ToString for list<int> rather than list<'a>
    pub(crate) fn is_instantiated_enum(&self) -> bool {
        let Some(ty) = self.single() else {
            return false;
        };
        match ty {
            // return true if an enumt with at least one parameter instantiated
            PotentialType::UdtInstance(_, _, tys) => !tys
                .iter()
                .all(|ty| matches!(ty.single(), Some(PotentialType::Poly(..)))),
            _ => false,
        }
    }

    fn underdetermined(&self) -> bool {
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
        BinOpcode::Equal => {
            let ty_left =
                TypeVar::make_poly_constrained(prov_left, "a".to_owned(), "Equal".to_owned());
            let ty_right =
                TypeVar::make_poly_constrained(prov_right, "a".to_owned(), "Equal".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            (ty_left, ty_right, TypeVar::make_bool(prov_out))
        }
    }
}

pub(crate) fn ast_type_to_statics_type_interface(
    ctx: &mut StaticsContext,
    ast_type: Rc<AstType>,
    interface_ident: Option<&String>,
) -> TypeVar {
    match &*ast_type.typekind {
        TypeKind::Poly(ident, interfaces) => {
            TypeVar::make_poly(Prov::Node(ast_type.id()), ident.clone(), interfaces.clone())
        }
        TypeKind::Name(ident) => {
            if let Some(interface_ident) = interface_ident {
                // TODO: Instead of checking equality with "self", it should get its own TypeKind. TypeKind::Self
                if ident == "self" {
                    TypeVar::make_poly_constrained(
                        Prov::Node(ast_type.id()),
                        "a".to_string(), //TODO: why "a"? Maybe use "self" or "Self" instead?
                        interface_ident.clone(),
                    )
                } else {
                    TypeVar::fresh(ctx, Prov::Alias(ident.clone()))
                }
            } else {
                TypeVar::fresh(ctx, Prov::Alias(ident.clone()))
            }
        }
        TypeKind::Ap(ident, params) => TypeVar::make_def_instance(
            Prov::Node(ast_type.id()),
            ident.clone(),
            params
                .iter()
                .map(|param| {
                    ast_type_to_statics_type_interface(ctx, param.clone(), interface_ident)
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
                .map(|t| ast_type_to_statics_type_interface(ctx, t.clone(), interface_ident))
                .collect(),
            ast_type_to_statics_type_interface(ctx, rhs.clone(), interface_ident),
            Prov::Node(ast_type.id()),
        ),
        TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_statics_type_interface(
                    ctx,
                    t.clone(),
                    interface_ident,
                ));
            }
            TypeVar::make_tuple(statics_types, Prov::Node(ast_type.id()))
        }
    }
}

pub(crate) fn ast_type_to_statics_type(ctx: &mut StaticsContext, ast_type: Rc<AstType>) -> TypeVar {
    ast_type_to_statics_type_interface(ctx, ast_type, None)
}

pub(crate) type Provs = RefCell<BTreeSet<Prov>>;

fn provs_singleton(prov: Prov) -> Provs {
    let mut set = BTreeSet::new();
    set.insert(prov);
    RefCell::new(set)
}

#[derive(Debug, Clone)]
pub(crate) enum Mode {
    Syn,
    Ana { expected: TypeVar },
}

pub(crate) fn constrain(mut expected: TypeVar, mut actual: TypeVar) {
    expected.0.union_with(&mut actual.0, TypeVarData::merge);
}

// TODO: rename to TypeEnv
// TODO: actually, it's not just a typ environment, it also handles resolving variables to their declarations
#[derive(Clone)]
pub(crate) struct Gamma {
    var_to_type: Environment<Identifier, TypeVar>,
    ty_vars_in_scope: Environment<Identifier, ()>,

    var_declarations: Environment<Identifier, Resolution>, // this is basically a local namespace
}
impl Gamma {
    pub(crate) fn empty() -> Self {
        Self {
            var_to_type: Environment::empty(),
            ty_vars_in_scope: Environment::empty(),

            var_declarations: Environment::empty(),
        }
    }

    pub(crate) fn extend(&self, ident: Identifier, ty: TypeVar) {
        self.var_to_type.extend(ident.clone(), ty);
    }

    pub(crate) fn extend_declaration(&self, symbol: Identifier, resolution: Resolution) {
        self.var_declarations.extend(symbol, resolution);
    }

    fn lookup_declaration(&self, symbol: &Identifier) -> Option<Resolution> {
        self.var_declarations.lookup(symbol)
    }

    fn add_polys(&self, ty: &TypeVar) {
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

    fn lookup(&self, id: &Identifier) -> Option<TypeVar> {
        self.var_to_type.lookup(id)
    }

    fn lookup_poly(&self, id: &Identifier) -> bool {
        self.ty_vars_in_scope.lookup(id).is_some()
    }

    fn new_scope(&self) -> Self {
        Self {
            var_to_type: self.var_to_type.new_scope(),
            ty_vars_in_scope: self.ty_vars_in_scope.new_scope(),

            var_declarations: self.var_declarations.new_scope(),
        }
    }
}

// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub(crate) fn result_of_constraint_solving(
    ctx: &mut StaticsContext,
    node_map: &NodeMap,
    sources: &Sources,
) -> Result<(), String> {
    // get list of type conflicts
    let mut type_conflicts = Vec::new();
    for potential_types in ctx.vars.values() {
        let type_suggestions = potential_types.0.clone_data().types; // TODO why not just check if it's solved?
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions.clone());
        }
    }

    // replace underdetermined types with unit
    if type_conflicts.is_empty() {
        for potential_types in ctx.vars.values() {
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
    for (ident, impls) in ctx.interface_impls.iter() {
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
                ctx.multiple_interface_impls
                    .insert(ident.clone(), impl_locs.clone());
            }
        }
    }

    let mut err_string = String::new();

    let mut bad_instantiations = false;
    // check for bad instantiation of polymorphic types constrained to an Interface
    for (typ, interfaces) in ctx.types_constrained_to_interfaces.iter() {
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
            } else if let Some(impl_list) = ctx.interface_impls.get(interface) {
                // find at least one implementation of interface that matches the type constrained to the interface
                for impl_ in impl_list {
                    if let Some(impl_ty) = impl_.typ.solution() {
                        if let Err((_err_monoty, _err_impl_ty)) =
                            ty_fits_impl_ty(ctx, typ.clone(), impl_ty.clone())
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
    for (typ, location) in ctx.types_that_must_be_structs.iter() {
        let typ = typ.solution();
        let Some(solved) = typ else {
            continue;
        };
        if let SolvedType::UdtInstance(ident, _) = &solved {
            let struct_def = ctx.struct_defs.get(ident);
            if struct_def.is_some() {
                continue;
            }
        }

        bad_field_access = true;
        let _ = writeln!(err_string, "error: type '{}' is not a struct", solved);
        let span = node_map.get(location).unwrap().span();
        span.display(&mut err_string, sources, "");
    }

    if ctx.unbound_vars.is_empty()
        && ctx.unbound_interfaces.is_empty()
        && type_conflicts.is_empty()
        && ctx.multiple_udt_defs.is_empty()
        && ctx.multiple_interface_defs.is_empty()
        && ctx.multiple_interface_impls.is_empty()
        && ctx.interface_impl_for_instantiated_ty.is_empty()
        && ctx.interface_impl_extra_method.is_empty()
        && ctx.interface_impl_missing_method.is_empty()
        && ctx.annotation_needed.is_empty()
        && ctx.field_not_ident.is_empty()
        && !bad_instantiations
        && !bad_field_access
    {
        for (node_id, node) in node_map.iter() {
            let ty = ctx.solution_of_node(*node_id);
            let _span = node.span();
            if let Some(_ty) = ty {}
        }
        return Ok(());
    }

    if !ctx.unbound_vars.is_empty() {
        err_string.push_str("You have unbound variables!\n");
        for ast_id in ctx.unbound_vars.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            span.display(&mut err_string, sources, "");
        }
    }
    if !ctx.unbound_interfaces.is_empty() {
        for ast_id in ctx.unbound_interfaces.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "Interface being implemented is not defined\n",
            );
        }
    }
    if !ctx.multiple_udt_defs.is_empty() {
        for (ident, enum_ids) in ctx.multiple_udt_defs.iter() {
            let _ = writeln!(err_string, "Multiple definitions for type {}, ident", ident);
            for ast_id in enum_ids {
                let span = node_map.get(ast_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }
        }
    }
    if !ctx.multiple_interface_defs.is_empty() {
        for (ident, interface_ids) in ctx.multiple_interface_defs.iter() {
            let _ = writeln!(err_string, "Multiple definitions for interface {}", ident);
            for ast_id in interface_ids {
                let span = node_map.get(ast_id).unwrap().span();
                span.display(&mut err_string, sources, "");
            }
        }
    }

    if !ctx.multiple_interface_impls.is_empty() {
        for (ident, impl_ids) in ctx.multiple_interface_impls.iter() {
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

    if !ctx.interface_impl_for_instantiated_ty.is_empty() {
        for ast_id in ctx.interface_impl_for_instantiated_ty.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            span.display(
                &mut err_string,
                sources,
                "Interface implementations for instantiated types are not supported.\n",
            );
        }
    }

    if !ctx.interface_impl_extra_method.is_empty() {
        for (id, impls) in ctx.interface_impl_extra_method.iter() {
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

    if !ctx.interface_impl_missing_method.is_empty() {
        for (id, method_names) in ctx.interface_impl_missing_method.iter() {
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

    if !ctx.annotation_needed.is_empty() {
        for id in ctx.annotation_needed.iter() {
            let span = node_map.get(id).unwrap().span();
            span.display(&mut err_string, sources, "this needs a type annotation");
        }
    }

    if !ctx.field_not_ident.is_empty() {
        for id in ctx.field_not_ident.iter() {
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
                    Prov::Effect(_) => 16,
                });
                for cause in provs_vec {
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
                                Prov::Builtin(builtin) => {
                                    let s = builtin.name();
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
            }
            writeln!(err_string).unwrap();
        }
    }

    Err(err_string)
}

pub(crate) fn generate_constraints_toplevel(
    gamma: Gamma,
    toplevel: Rc<Toplevel>,
    ctx: &mut StaticsContext,
) {
    for (i, eff) in ctx.effects.iter().enumerate() {
        let prov = Prov::Effect(i as u16);
        let mut args = Vec::new();
        for arg in eff.type_signature.0.iter() {
            args.push(monotype_to_typevar(arg.clone(), prov.clone()));
        }
        let typ = TypeVar::make_func(
            args,
            monotype_to_typevar(eff.type_signature.1.clone(), prov.clone()),
            prov,
        );
        gamma.extend(eff.name.clone(), typ);
        gamma.extend_declaration(eff.name.clone(), Resolution::Effect(i as u16));
    }
    for builtin in Builtin::enumerate().iter() {
        let prov = Prov::Builtin(*builtin);
        let typ = solved_type_to_typevar(builtin.type_signature(), prov);
        gamma.extend(builtin.name(), typ);
        gamma.extend_declaration(builtin.name(), Resolution::Builtin(*builtin));
    }
    for statement in toplevel.statements.iter() {
        generate_constraints_stmt(gamma.clone(), Mode::Syn, statement.clone(), ctx, true);
    }
}

fn generate_constraints_expr(gamma: Gamma, mode: Mode, expr: Rc<Expr>, ctx: &mut StaticsContext) {
    let node_ty = TypeVar::from_node(ctx, expr.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(node_ty.clone(), expected),
    };
    match &*expr.kind {
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
        ExprKind::Str(s) => {
            constrain(node_ty, TypeVar::make_string(Prov::Node(expr.id)));
            let len = ctx.string_constants.len();
            ctx.string_constants.entry(s.clone()).or_insert(len);
        }
        ExprKind::List(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(expr.id).into()));
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
                    ctx,
                );
            }
        }
        ExprKind::Array(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(expr.id).into()));
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
                    ctx,
                );
            }
        }
        ExprKind::Identifier(symbol) => {
            let lookup = gamma.lookup_declaration(symbol);
            if let Some(resolution) = lookup {
                ctx.name_resolutions.insert(expr.id, resolution);
            }
            let lookup = gamma.lookup(symbol);
            if let Some(typ) = lookup {
                // replace polymorphic types with unifvars if necessary
                let typ = typ.instantiate(gamma, ctx, Prov::Node(expr.id));
                constrain(typ, node_ty);
                return;
            }
            // TODO: this is incredibly hacky. No respect for scope at all... Should be added at the toplevel with Effects at the least...
            let enum_def = ctx.enum_def_of_variant(symbol);
            if let Some(enum_def) = enum_def {
                let nparams = enum_def.params.len();
                let mut params = vec![];
                let mut substitution = BTreeMap::new();
                for i in 0..nparams {
                    params.push(TypeVar::fresh(
                        ctx,
                        Prov::InstantiateUdtParam(Box::new(Prov::Node(expr.id)), i as u8),
                    ));
                    substitution.insert(enum_def.params[i].clone(), params[i].clone());
                }
                let def_type = TypeVar::make_def_instance(
                    Prov::UdtDef(Box::new(Prov::Node(expr.id))),
                    enum_def.name,
                    params,
                );

                let the_variant = enum_def
                    .variants
                    .iter()
                    .find(|v| v.ctor == *symbol)
                    .unwrap();
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
            let struct_def = ctx.struct_defs.get(symbol).cloned();
            if let Some(struct_def) = struct_def {
                let nparams = struct_def.params.len();
                let mut params = vec![];
                let mut substitution = BTreeMap::new();
                for i in 0..nparams {
                    params.push(TypeVar::fresh(
                        ctx,
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
            ctx.unbound_vars.insert(expr.id());
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op, expr.id);
            let (ty_left, ty_right, ty_out) = (
                ty_left.instantiate(gamma.clone(), ctx, Prov::Node(expr.id)),
                ty_right.instantiate(gamma.clone(), ctx, Prov::Node(expr.id)),
                ty_out.instantiate(gamma.clone(), ctx, Prov::Node(expr.id)),
            );
            constrain(ty_out, node_ty);
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana { expected: ty_left },
                left.clone(),
                ctx,
            );
            generate_constraints_expr(gamma, Mode::Ana { expected: ty_right }, right.clone(), ctx);
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
                    ctx,
                    true,
                );
            }
            // if last statement is an expression, the block will have that expression's type
            if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().kind {
                generate_constraints_expr(
                    new_gamma,
                    Mode::Ana { expected: node_ty },
                    terminal_expr.clone(),
                    ctx,
                )
            } else {
                generate_constraints_stmt(
                    new_gamma,
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                    ctx,
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
                ctx,
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
                        ctx,
                    );
                    generate_constraints_expr(
                        gamma,
                        Mode::Ana { expected: node_ty },
                        expr2.clone(),
                        ctx,
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
                        ctx,
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
                ctx,
            );
            generate_constraints_expr(gamma, Mode::Syn, expr.clone(), ctx);
            constrain(node_ty, TypeVar::make_unit(Prov::Node(expr.id)))
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = TypeVar::from_node(ctx, scrut.id);
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: ty_scrutiny.clone(),
                },
                scrut.clone(),
                ctx,
            );
            for arm in arms {
                let new_gamma = gamma.new_scope();
                generate_constraints_pat(
                    new_gamma.clone(),
                    Mode::Ana {
                        expected: ty_scrutiny.clone(),
                    },
                    arm.pat.clone(),
                    ctx,
                );
                generate_constraints_expr(
                    new_gamma,
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
            let body_gamma = gamma.new_scope();
            let ty_func = generate_constraints_func_helper(
                ctx,
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
                    let unknown =
                        TypeVar::fresh(ctx, Prov::FuncArg(Box::new(Prov::Node(func.id)), n as u8));
                    generate_constraints_expr(
                        gamma.clone(),
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
            constrain(ty_body.clone(), node_ty);

            // function type
            let ty_func = TypeVar::make_func(tys_args, ty_body, Prov::Node(expr.id));
            generate_constraints_expr(
                gamma,
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
            constrain(node_ty, TypeVar::make_tuple(tys, Prov::Node(expr.id)));
            for expr in exprs {
                generate_constraints_expr(gamma.clone(), Mode::Syn, expr.clone(), ctx);
            }
        }
        ExprKind::MemberAccess(expr, field) => {
            generate_constraints_expr(gamma, Mode::Syn, expr.clone(), ctx);
            let ty_expr = TypeVar::fresh(ctx, Prov::Node(expr.id));
            if ty_expr.underdetermined() {
                ctx.annotation_needed.insert(expr.id);
                return;
            }
            let Some(inner) = ty_expr.single() else {
                return;
            };
            if let PotentialType::UdtInstance(_, ident, _) = inner {
                if let Some(struct_def) = ctx.struct_defs.get(&ident) {
                    let ExprKind::Identifier(field_ident) = &*field.kind else {
                        ctx.field_not_ident.insert(field.id);
                        return;
                    };
                    let ty_field = TypeVar::fresh(
                        ctx,
                        Prov::StructField(field_ident.clone(), struct_def.location),
                    );
                    constrain(node_ty.clone(), ty_field);
                    return;
                }
            }

            ctx.types_that_must_be_structs.insert(ty_expr, expr.id);
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(gamma.clone(), Mode::Syn, accessed.clone(), ctx);

            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(Prov::Node(accessed.id).into()));
            let accessed_ty = TypeVar::from_node(ctx, accessed.id);
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
                ctx,
            );

            constrain(node_ty, elem_ty);
        }
    }
}

fn generate_constraints_func_helper(
    ctx: &mut StaticsContext,
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
            let ty_pat = TypeVar::from_node(ctx, arg.id);
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(ctx, arg_annot.id());
                    let arg_annot = ast_type_to_statics_type(ctx, arg_annot.clone());
                    constrain(ty_annot.clone(), arg_annot.clone());
                    gamma.add_polys(&arg_annot);
                    generate_constraints_pat(
                        gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                        Mode::Ana { expected: ty_annot },
                        arg.clone(),
                        ctx,
                    )
                }
                None => generate_constraints_pat(gamma.clone(), Mode::Syn, arg.clone(), ctx),
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(Box::new(Prov::Node(node_id))));
    generate_constraints_expr(
        gamma.clone(),
        Mode::Ana {
            expected: ty_body.clone(),
        },
        body.clone(),
        ctx,
    );
    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_statics_type(ctx, out_annot.clone());
        gamma.add_polys(&out_annot);
        generate_constraints_expr(
            gamma,
            Mode::Ana {
                expected: out_annot,
            },
            body.clone(),
            ctx,
        );
    }

    TypeVar::make_func(ty_args, ty_body, Prov::Node(node_id))
}

fn generate_constraints_stmt(
    gamma: Gamma,
    mode: Mode,
    stmt: Rc<Stmt>,
    ctx: &mut StaticsContext,
    add_to_tyvar_gamma: bool,
) {
    match &*stmt.kind {
        StmtKind::InterfaceDef(..) => {}
        StmtKind::Import(..) => {}
        StmtKind::InterfaceImpl(ident, typ, statements) => {
            let typ = ast_type_to_statics_type(ctx, typ.clone());

            if let Some(interface_def) = ctx.interface_def_of_ident(ident) {
                for statement in statements {
                    let StmtKind::FuncDef(pat, _args, _out, _body) = &*statement.kind else {
                        continue;
                    };
                    let method_name = pat.kind.get_identifier_of_variable();
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

                        constrain(expected, TypeVar::from_node(ctx, pat.id));

                        generate_constraints_stmt(
                            gamma.clone(),
                            Mode::Syn,
                            statement.clone(),
                            ctx,
                            false,
                        );
                    } else {
                        ctx.interface_impl_extra_method
                            .entry(stmt.id)
                            .or_default()
                            .push(statement.id);
                    }
                }
                for interface_method in interface_def.methods {
                    if !statements.iter().any(|stmt| match &*stmt.kind {
                        StmtKind::FuncDef(pat, _args, _out, _body) => {
                            pat.kind.get_identifier_of_variable() == interface_method.name
                        }
                        _ => false,
                    }) {
                        ctx.interface_impl_missing_method
                            .entry(stmt.id)
                            .or_default()
                            .push(interface_method.name.clone());
                    }
                }
            } else {
                ctx.unbound_interfaces.insert(stmt.id);
            }
        }
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(ident, ty) => {
                let left = TypeVar::fresh(ctx, Prov::Alias(ident.clone()));
                let right = ast_type_to_statics_type(ctx, ty.clone());
                constrain(left, right);
            }
            TypeDefKind::Enum(..) | TypeDefKind::Struct(..) => {}
        },
        StmtKind::Expr(expr) => {
            generate_constraints_expr(gamma, mode, expr.clone(), ctx);
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            let ty_pat = TypeVar::from_node(ctx, pat.id);

            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                ctx,
            );

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_statics_type(ctx, ty_ann.clone());
                gamma.add_polys(&ty_ann);
                generate_constraints_pat(gamma, Mode::Ana { expected: ty_ann }, pat.clone(), ctx)
            } else {
                generate_constraints_pat(gamma, Mode::Syn, pat.clone(), ctx)
            };
        }
        StmtKind::Set(lhs, rhs) => {
            let ty_lhs = TypeVar::from_node(ctx, lhs.id);
            generate_constraints_expr(gamma.clone(), Mode::Syn, lhs.clone(), ctx);
            let ty_rhs = TypeVar::from_node(ctx, rhs.id);
            generate_constraints_expr(gamma, Mode::Syn, rhs.clone(), ctx);
            constrain(ty_lhs, ty_rhs);
        }
        StmtKind::FuncDef(name, args, out_annot, body) => {
            let func_node_id = stmt.id;
            let ty_pat = TypeVar::from_node(ctx, name.id);

            let func_name = name.kind.get_identifier_of_variable();

            // TODO this needs a better explanation
            if add_to_tyvar_gamma {
                gamma.extend(name.kind.get_identifier_of_variable(), ty_pat.clone());
                gamma.extend_declaration(
                    func_name,
                    Resolution::FreeFunction(stmt.id, name.kind.get_identifier_of_variable()),
                );
            } else {
                gamma.extend_declaration(func_name.clone(), Resolution::InterfaceMethod(func_name));
            }

            let body_gamma = gamma.new_scope();
            let ty_func = generate_constraints_func_helper(
                ctx,
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

fn generate_constraints_pat(gamma: Gamma, mode: Mode, pat: Rc<Pat>, ctx: &mut StaticsContext) {
    let ty_pat = TypeVar::from_node(ctx, pat.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(expected, ty_pat.clone()),
    };
    match &*pat.kind {
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
            gamma.extend_declaration(identifier.clone(), Resolution::Var(pat.id));
        }
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => TypeVar::from_node(ctx, data.id),
                None => TypeVar::make_unit(Prov::VariantNoData(Box::new(Prov::Node(pat.id)))),
            };
            let mut substitution = BTreeMap::new();
            let ty_enum_instance = {
                let enum_def = ctx.enum_def_of_variant(tag);

                if let Some(enum_def) = enum_def {
                    let nparams = enum_def.params.len();
                    let mut params = vec![];
                    for i in 0..nparams {
                        params.push(TypeVar::fresh(
                            ctx,
                            Prov::InstantiateUdtParam(Box::new(Prov::Node(pat.id)), i as u8),
                        ));
                        substitution.insert(enum_def.params[i].clone(), params[i].clone());
                    }
                    let def_type = TypeVar::make_def_instance(
                        Prov::UdtDef(Box::new(Prov::Node(pat.id))),
                        enum_def.name,
                        params,
                    );

                    let variant_def = enum_def.variants.iter().find(|v| v.ctor == *tag).unwrap();
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

            constrain(ty_pat, ty_enum_instance);
            if let Some(data) = data {
                generate_constraints_pat(gamma, Mode::Ana { expected: ty_data }, data.clone(), ctx)
            };
        }
        PatKind::Tuple(pats) => {
            let tys_elements = pats
                .iter()
                .map(|pat| TypeVar::fresh(ctx, Prov::Node(pat.id)))
                .collect();
            constrain(
                ty_pat,
                TypeVar::make_tuple(tys_elements, Prov::Node(pat.id)),
            );
            for pat in pats {
                generate_constraints_pat(gamma.clone(), Mode::Syn, pat.clone(), ctx)
            }
        }
    }
}

pub(crate) fn monotype_to_typevar(ty: Monotype, prov: Prov) -> TypeVar {
    match ty {
        Monotype::Unit => TypeVar::make_unit(prov),
        Monotype::Int => TypeVar::make_int(prov),
        Monotype::Float => TypeVar::make_float(prov),
        Monotype::Bool => TypeVar::make_bool(prov),
        Monotype::String => TypeVar::make_string(prov),
        Monotype::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|e| monotype_to_typevar(e, prov.clone()))
                .collect();
            TypeVar::make_tuple(elements, prov)
        }
        Monotype::Function(args, out) => {
            let args = args
                .into_iter()
                .map(|a| monotype_to_typevar(a, prov.clone()))
                .collect();
            let out = monotype_to_typevar(*out, prov.clone());
            TypeVar::make_func(args, out, prov.clone())
        }
        Monotype::Enum(name, params) => {
            let params = params
                .into_iter()
                .map(|p| monotype_to_typevar(p, prov.clone()))
                .collect();
            TypeVar::make_def_instance(prov, name, params)
        }
    }
}

pub(crate) fn solved_type_to_typevar(ty: SolvedType, prov: Prov) -> TypeVar {
    match ty {
        SolvedType::Unit => TypeVar::make_unit(prov),
        SolvedType::Int => TypeVar::make_int(prov),
        SolvedType::Float => TypeVar::make_float(prov),
        SolvedType::Bool => TypeVar::make_bool(prov),
        SolvedType::String => TypeVar::make_string(prov),
        SolvedType::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|e| solved_type_to_typevar(e, prov.clone()))
                .collect();
            TypeVar::make_tuple(elements, prov)
        }
        SolvedType::Function(args, out) => {
            let args = args
                .into_iter()
                .map(|a| solved_type_to_typevar(a, prov.clone()))
                .collect();
            let out = solved_type_to_typevar(*out, prov.clone());
            TypeVar::make_func(args, out, prov.clone())
        }
        SolvedType::UdtInstance(name, params) => {
            let params = params
                .into_iter()
                .map(|p| solved_type_to_typevar(p, prov.clone()))
                .collect();
            TypeVar::make_def_instance(prov, name, params)
        }
        SolvedType::Poly(ident, interfaces) => TypeVar::make_poly(prov, ident, interfaces),
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

// TODO: there should be a file separate from typecheck that just has stuff pertaining to Types that the whole compiler can use
// type-utils or just types.rs
pub(crate) fn ty_fits_impl_ty(
    ctx: &StaticsContext,
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
    ctx: &StaticsContext,
    typ: SolvedType,
    interfaces: BTreeSet<Identifier>,
) -> bool {
    for interface in interfaces {
        if let SolvedType::Poly(_, interfaces2) = &typ {
            // if 'a Interface1 is constrained to [Interfaces...], ignore
            if interfaces2.contains(&interface) {
                return true;
            }
        }
        if let Some(impl_list) = ctx.interface_impls.get(&interface) {
            // find at least one implementation of interface that matches the type constrained to the interface
            for impl_ in impl_list {
                if let Some(impl_ty) = impl_.typ.solution() {
                    if ty_fits_impl_ty(ctx, typ.clone(), impl_ty).is_ok() {
                        return true;
                    }
                }
            }
        }
    }
    false
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
