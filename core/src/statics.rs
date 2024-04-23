use crate::ast::{
    self, Expr, ExprKind, Identifier, Node, Pat, PatKind, Stmt, StmtKind, TypeDefKind,
};
use crate::operators::BinOpcode;
use core::panic;

use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::{self, Write};
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    // a type which must be solved for (skolem)
    UnifVar(UnifVar),

    // "type must be equal to this"
    Poly(Provs, Identifier, Vec<Identifier>), // type name, then list of Interfaces it must match
    Unit(Provs),
    Int(Provs),
    Float(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<Type>, Box<Type>),
    Tuple(Provs, Vec<Type>),
    AdtInstance(Provs, Identifier, Vec<Type>),
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
    Adt(Identifier, Vec<TypeMonomorphized>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct AdtDef {
    pub name: Identifier,
    pub params: Vec<Identifier>,
    pub variants: Vec<Variant>,
    pub location: ast::Id,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Variant {
    pub ctor: Identifier,
    pub data: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceDef {
    pub name: Identifier,
    pub methods: Vec<InterfaceDefMethod>,
    pub location: ast::Id,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceImpl {
    pub name: Identifier,
    pub typ: Type,
    pub methods: Vec<InterfaceImplMethod>,
    pub location: ast::Id,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceDefMethod {
    pub name: Identifier,
    pub ty: Type,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct InterfaceImplMethod {
    pub name: Identifier,
    pub method_location: ast::Id,
    pub identifier_location: ast::Id,
}

pub type UnifVar = UnionFindNode<UnifVarData>;

#[derive(Debug, Clone, PartialEq)]
pub struct UnifVarData {
    pub types: BTreeMap<TypeKey, Type>,
}

impl UnifVarData {
    pub fn solution(&self) -> Option<Type> {
        if self.types.len() == 1 {
            self.types.values().next().unwrap().solution()
        } else {
            None
        }
    }
}

// If two types don't share the same key, they must be in conflict
// (If two types share the same key, they may or may not be in conflict)
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeKey {
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
// (1) track the origins (plural!) of a type solution
// (2) give the *unique* identity of an unknown type variable (UnifVar) in the SolutionMap
// TODO: Does Prov really need to be that deeply nested? Will there really be FuncArg -> InstantiatedPoly -> BinopLeft -> Node? Or can we simplify here?
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Prov {
    Node(ast::Id),   // the type of an expression or statement
    Builtin(String), // a function or constant, which doesn't exist in the AST
    UnderdeterminedCoerceToUnit,

    Alias(Identifier), // TODO add Box<Prov>
    AdtDef(Box<Prov>),

    InstantiateAdtParam(Box<Prov>, u8),
    InstantiatePoly(Box<Prov>, Identifier),
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
    BinopLeft(Box<Prov>),
    BinopRight(Box<Prov>),
    ListElem(Box<Prov>),
    VariantNoData(Box<Prov>), // the type of the data of a variant with no data, always Unit.
}

impl Prov {
    // TODO: Can we make this not Optional? Only reason it would fail is if the last prov in the chain is a builtin
    // TODO: remove Builtin prov for this reason, defeats the purpose. Builtins should be declared in the PRELUDE, and that declaration will be the Prov.
    pub fn get_location(&self) -> Option<ast::Id> {
        match self {
            Prov::Node(id) => Some(*id),
            Prov::Builtin(_) => None,
            Prov::UnderdeterminedCoerceToUnit => None,
            Prov::Alias(_) => None,
            Prov::AdtDef(inner)
            | Prov::InstantiateAdtParam(inner, _)
            | Prov::InstantiatePoly(inner, _)
            | Prov::FuncArg(inner, _)
            | Prov::FuncOut(inner)
            | Prov::BinopLeft(inner)
            | Prov::BinopRight(inner)
            | Prov::ListElem(inner)
            | Prov::VariantNoData(inner) => inner.get_location(),
        }
    }
}

impl Type {
    pub fn key(&self) -> Option<TypeKey> {
        match self {
            Type::UnifVar(_) => None,
            Type::Poly(_, _, _) => Some(TypeKey::Poly),
            Type::Unit(_) => Some(TypeKey::Unit),
            Type::Int(_) => Some(TypeKey::Int),
            Type::Float(_) => Some(TypeKey::Float),
            Type::Bool(_) => Some(TypeKey::Bool),
            Type::String(_) => Some(TypeKey::String),
            Type::Function(_, args, _) => Some(TypeKey::Function(args.len() as u8)),
            Type::Tuple(_, elems) => Some(TypeKey::Tuple(elems.len() as u8)),
            Type::AdtInstance(_, ident, params) => {
                Some(TypeKey::TyApp(ident.clone(), params.len() as u8))
            }
        }
    }

    // Creates a clone of a Type with polymorphic variables not in scope replaced with fresh unification variables
    // Cloning type variables is very subtle...
    pub fn instantiate(
        self,
        gamma: Rc<RefCell<Gamma>>,
        inf_ctx: &mut InferenceContext,
        prov: Prov,
    ) -> Type {
        match self {
            Type::Unit(_) | Type::Int(_) | Type::Float(_) | Type::Bool(_) | Type::String(_) => {
                self // noop
            }
            Type::UnifVar(unifvar) => {
                let data = unifvar.clone_data();
                // To avoid confusing error feedback, only specialize a unifvar if it has a single type so far
                if data.types.len() == 1 {
                    let ty = data.types.into_values().next().unwrap();
                    if let Type::Poly(_, _, ref _interfaces) = ty {
                        //
                        ty.instantiate(gamma, inf_ctx, prov)
                    } else {
                        //
                        let ty = ty.instantiate(gamma, inf_ctx, prov.clone());
                        let mut types = BTreeMap::new();
                        types.insert(ty.key().unwrap(), ty);
                        let data_instantiated = UnifVarData { types };

                        let unifvar = UnionFindNode::new(data_instantiated);
                        inf_ctx.vars.insert(prov, unifvar.clone());
                        Type::UnifVar(unifvar)
                    }
                } else {
                    //
                    Type::UnifVar(unifvar) // noop
                }
            }
            Type::Poly(_, ref ident, ref interfaces) => {
                if !gamma.borrow().lookup_poly(ident) {
                    let ret = Type::fresh_unifvar(
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
                    ret
                } else {
                    self // noop
                }
            }
            Type::AdtInstance(provs, ident, params) => {
                //
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                Type::AdtInstance(provs, ident, params)
            }
            Type::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                let out = Box::new(out.instantiate(gamma, inf_ctx, prov));
                Type::Function(provs, args, out)
            }
            Type::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                Type::Tuple(provs, elems)
            }
        }
    }

    // Creates a clone of a Type with polymorphic variabels replaced by subtitutions
    pub fn subst(
        self,
        gamma: Rc<RefCell<Gamma>>,
        inf_ctx: &mut InferenceContext,
        prov: Prov,
        substitution: &BTreeMap<Identifier, Type>,
    ) -> Type {
        match self {
            Type::Unit(_) | Type::Int(_) | Type::Float(_) | Type::Bool(_) | Type::String(_) => {
                self // noop
            }
            Type::UnifVar(unifvar) => {
                let data = unifvar.clone_data();
                if data.types.len() == 1 {
                    let ty = data.types.into_values().next().unwrap();
                    if let Type::Poly(_, _, ref _interfaces) = ty {
                        ty.subst(gamma, inf_ctx, prov, substitution)
                    } else {
                        let ty = ty.subst(gamma, inf_ctx, prov.clone(), substitution);
                        let mut types = BTreeMap::new();
                        types.insert(ty.key().unwrap(), ty);
                        let data_instantiated = UnifVarData { types };

                        let unifvar = UnionFindNode::new(data_instantiated);
                        inf_ctx.vars.insert(prov, unifvar.clone());
                        Type::UnifVar(unifvar)
                    }
                } else {
                    Type::UnifVar(unifvar) // noop
                }
            }
            Type::Poly(_, ref ident, ref _interfaces) => {
                if let Some(ty) = substitution.get(ident) {
                    ty.clone()
                } else {
                    self // noop
                }
            }
            Type::AdtInstance(provs, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.subst(gamma.clone(), inf_ctx, prov.clone(), substitution))
                    .collect();
                Type::AdtInstance(provs, ident, params)
            }
            Type::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.subst(gamma.clone(), inf_ctx, prov.clone(), substitution))
                    .collect();
                let out = Box::new(out.subst(gamma, inf_ctx, prov, substitution));
                Type::Function(provs, args, out)
            }
            Type::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.subst(gamma.clone(), inf_ctx, prov.clone(), substitution))
                    .collect();
                Type::Tuple(provs, elems)
            }
        }
    }

    pub fn from_node(inf_ctx: &mut InferenceContext, id: ast::Id) -> Type {
        let prov = Prov::Node(id);
        Type::fresh_unifvar(inf_ctx, prov)
    }

    pub fn solution_of_node(inf_ctx: &InferenceContext, id: ast::Id) -> Option<Type> {
        let prov = Prov::Node(id);
        match inf_ctx.vars.get(&prov) {
            Some(unifvar) => unifvar.clone_data().solution(),
            None => None,
        }
    }

    pub fn fresh_unifvar(inf_ctx: &mut InferenceContext, prov: Prov) -> Type {
        match inf_ctx.vars.get(&prov) {
            Some(ty) => Type::UnifVar(ty.clone()),
            None => {
                let ty_var = UnifVar::new(UnifVarData::empty());
                let ty = Type::UnifVar(ty_var.clone());
                inf_ctx.vars.insert(prov, ty_var);
                ty
            }
        }
    }

    pub fn make_poly(prov: Prov, ident: String, interfaces: Vec<String>) -> Type {
        Type::Poly(provs_singleton(prov), ident, interfaces)
    }

    pub fn make_poly_constrained(prov: Prov, ident: String, interface_ident: String) -> Type {
        Type::Poly(provs_singleton(prov), ident, vec![interface_ident])
    }

    pub fn make_def_instance(prov: Prov, ident: String, params: Vec<Type>) -> Type {
        Type::AdtInstance(provs_singleton(prov), ident, params)
    }

    pub fn make_unit(prov: Prov) -> Type {
        Type::Unit(provs_singleton(prov))
    }

    pub fn make_int(prov: Prov) -> Type {
        Type::Int(provs_singleton(prov))
    }

    pub fn make_float(prov: Prov) -> Type {
        Type::Float(provs_singleton(prov))
    }

    pub fn make_bool(prov: Prov) -> Type {
        Type::Bool(provs_singleton(prov))
    }

    pub fn make_string(prov: Prov) -> Type {
        Type::String(provs_singleton(prov))
    }

    pub fn make_arrow(args: Vec<Type>, out: Type, prov: Prov) -> Type {
        Type::Function(provs_singleton(prov), args, out.into())
    }

    pub fn make_tuple(elems: Vec<Type>, prov: Prov) -> Type {
        Type::Tuple(provs_singleton(prov), elems)
    }

    pub fn provs(&self) -> &Provs {
        match self {
            Self::UnifVar(_) => panic!("Type::provs called on Type::Var"),
            Self::Poly(provs, _, _)
            | Self::Unit(provs)
            | Self::Int(provs)
            | Self::Float(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _)
            | Self::AdtInstance(provs, _, _) => provs,
        }
    }

    pub fn solution(&self) -> Option<Type> {
        match self {
            Self::Bool(_)
            | Self::Int(_)
            | Self::Float(_)
            | Self::String(_)
            | Self::Unit(_)
            | Self::Poly(_, _, _) => Some(self.clone()),
            Self::Function(provs, args, out) => {
                let mut args2: Vec<Type> = vec![];
                for arg in args {
                    if let Some(arg) = arg.solution() {
                        args2.push(arg);
                    } else {
                        return None;
                    }
                }
                let out = out.solution()?;
                Some(Type::Function(provs.clone(), args2, out.into()))
            }
            Self::Tuple(provs, elems) => {
                let mut elems2: Vec<Type> = vec![];
                for elem in elems {
                    if let Some(elem) = elem.solution() {
                        elems2.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(Type::Tuple(provs.clone(), elems2))
            }
            Self::AdtInstance(provs, ident, params) => {
                let mut params2: Vec<Type> = vec![];
                for param in params {
                    if let Some(param) = param.solution() {
                        params2.push(param);
                    } else {
                        return None;
                    }
                }
                Some(Type::AdtInstance(provs.clone(), ident.clone(), params2))
            }
            Self::UnifVar(unifvar) => unifvar.clone_data().solution(),
        }
    }

    pub fn instance_type(&self) -> Option<TypeMonomorphized> {
        match self {
            Self::UnifVar(_) => None,
            Self::Poly(_, _ident, _interfaces) => None,
            Self::Unit(_) => Some(TypeMonomorphized::Unit),
            Self::Int(_) => Some(TypeMonomorphized::Int),
            Self::Float(_) => Some(TypeMonomorphized::Float),
            Self::Bool(_) => Some(TypeMonomorphized::Bool),
            Self::String(_) => Some(TypeMonomorphized::String),
            Self::Function(_, args, out) => {
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
            Self::Tuple(_, _elems) => {
                let mut elems2 = vec![];
                for elem in _elems {
                    if let Some(elem) = elem.instance_type() {
                        elems2.push(elem);
                    } else {
                        return None;
                    }
                }
                Some(TypeMonomorphized::Tuple(elems2))
            }
            Self::AdtInstance(_, ident, params) => {
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

    pub fn is_overloaded(&self) -> bool {
        match self {
            Self::UnifVar(_) => false,
            Self::Poly(_, _, interfaces) => !interfaces.is_empty(),
            Self::Unit(_) => false,
            Self::Int(_) => false,
            Self::Float(_) => false,
            Self::Bool(_) => false,
            Self::String(_) => false,
            Self::Function(_, args, out) => {
                args.iter().any(|ty| ty.is_overloaded()) || out.is_overloaded()
            }
            Self::Tuple(_, tys) => tys.iter().any(|ty| ty.is_overloaded()),
            Self::AdtInstance(_, _, _tys) => false,
        }
    }

    // return true if the type is an adt with at least one parameter instantiated
    // this is used to see if an implementation of an interface is for an instantiated adt, which is not allowed
    // example: implement ToString for list<int> rather than list<'a>
    pub fn is_instantiated_adt(&self) -> bool {
        match self {
            // return true if an adt with at least one parameter instantiated
            Self::AdtInstance(_, _, tys) => !tys.iter().all(|ty| matches!(ty, Self::Poly(..))),
            _ => false,
        }
    }

    pub fn is_unit(&self) -> bool {
        matches!(self, Self::Unit(_))
    }
}

pub fn types_of_binop(opcode: &BinOpcode, id: ast::Id) -> (Type, Type, Type) {
    let prov_left = Prov::BinopLeft(Prov::Node(id).into());
    let prov_right = Prov::BinopRight(Prov::Node(id).into());
    let prov_out = Prov::Node(id);
    match opcode {
        BinOpcode::And | BinOpcode::Or => (
            Type::make_bool(prov_left),
            Type::make_bool(prov_right),
            Type::make_bool(prov_out),
        ),
        BinOpcode::Add
        | BinOpcode::Subtract
        | BinOpcode::Multiply
        | BinOpcode::Divide
        | BinOpcode::Pow => {
            let ty_left = Type::make_poly_constrained(prov_left, "a".to_owned(), "Num".to_owned());
            let ty_right =
                Type::make_poly_constrained(prov_right, "a".to_owned(), "Num".to_owned());
            let ty_out = Type::make_poly_constrained(prov_out, "a".to_owned(), "Num".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            constrain(ty_left.clone(), ty_out.clone());
            (ty_left, ty_right, ty_out)
        }
        BinOpcode::Mod => (
            Type::make_int(prov_left),
            Type::make_int(prov_right),
            Type::make_int(prov_out),
        ),
        BinOpcode::LessThan
        | BinOpcode::GreaterThan
        | BinOpcode::LessThanOrEqual
        | BinOpcode::GreaterThanOrEqual => {
            let ty_left = Type::make_poly_constrained(prov_left, "a".to_owned(), "Num".to_owned());
            let ty_right =
                Type::make_poly_constrained(prov_right, "a".to_owned(), "Num".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            let ty_out = Type::make_bool(prov_out);
            (ty_left, ty_right, ty_out)
        }
        BinOpcode::Concat => (
            Type::make_string(prov_left),
            Type::make_string(prov_right),
            Type::make_string(prov_out),
        ),
        BinOpcode::Equals => {
            let ty_left =
                Type::make_poly_constrained(prov_left, "a".to_owned(), "Equals".to_owned());
            let ty_right =
                Type::make_poly_constrained(prov_right, "a".to_owned(), "Equals".to_owned());
            constrain(ty_left.clone(), ty_right.clone());
            (ty_left, ty_right, Type::make_bool(prov_out))
        }
    }
}

pub fn ast_type_to_statics_type_interface(
    inf_ctx: &mut InferenceContext,
    ast_type: Rc<ast::AstType>,
    interface_ident: Option<&String>,
) -> Type {
    match &*ast_type.typekind {
        ast::TypeKind::Poly(ident, interfaces) => {
            Type::make_poly(Prov::Node(ast_type.id()), ident.clone(), interfaces.clone())
        }
        ast::TypeKind::Alias(ident) => {
            if let Some(interface_ident) = interface_ident {
                if ident == "self" {
                    Type::make_poly_constrained(
                        Prov::Node(ast_type.id()),
                        "a".to_string(),
                        interface_ident.clone(),
                    )
                } else {
                    Type::fresh_unifvar(inf_ctx, Prov::Alias(ident.clone()))
                }
            } else {
                Type::fresh_unifvar(inf_ctx, Prov::Alias(ident.clone()))
            }
        }
        ast::TypeKind::Ap(ident, params) => Type::AdtInstance(
            provs_singleton(Prov::Node(ast_type.id())),
            ident.clone(),
            params
                .iter()
                .map(|param| {
                    ast_type_to_statics_type_interface(inf_ctx, param.clone(), interface_ident)
                })
                .collect(),
        ),
        ast::TypeKind::Unit => Type::make_unit(Prov::Node(ast_type.id())),
        ast::TypeKind::Int => Type::make_int(Prov::Node(ast_type.id())),
        ast::TypeKind::Float => Type::make_float(Prov::Node(ast_type.id())),
        ast::TypeKind::Bool => Type::make_bool(Prov::Node(ast_type.id())),
        ast::TypeKind::Str => Type::make_string(Prov::Node(ast_type.id())),
        ast::TypeKind::Function(lhs, rhs) => Type::make_arrow(
            lhs.iter()
                .map(|t| ast_type_to_statics_type_interface(inf_ctx, t.clone(), interface_ident))
                .collect(),
            ast_type_to_statics_type_interface(inf_ctx, rhs.clone(), interface_ident),
            Prov::Node(ast_type.id()),
        ),
        ast::TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_statics_type_interface(
                    inf_ctx,
                    t.clone(),
                    interface_ident,
                ));
            }
            Type::make_tuple(statics_types, Prov::Node(ast_type.id()))
        }
    }
}

pub fn ast_type_to_statics_type(
    inf_ctx: &mut InferenceContext,
    ast_type: Rc<ast::AstType>,
) -> Type {
    ast_type_to_statics_type_interface(inf_ctx, ast_type, None)
}

pub type Provs = RefCell<BTreeSet<Prov>>;

pub fn provs_singleton(prov: Prov) -> Provs {
    let mut set = BTreeSet::new();
    set.insert(prov);
    RefCell::new(set)
}

#[derive(Default)]
pub struct InferenceContext {
    // unification variables (skolems) which must be solved
    pub vars: HashMap<Prov, UnifVar>,

    // nominal type definitions (ADTs)
    pub adt_defs: HashMap<Identifier, AdtDef>,
    // map from variant names to ADT names
    pub variants_to_adt: HashMap<Identifier, Identifier>,

    // function definition locations
    pub fun_defs: HashMap<Identifier, Rc<Stmt>>,

    // BOOKKEEPING

    // interface definitions
    pub interface_defs: HashMap<Identifier, InterfaceDef>,
    // map from methods to interface names
    pub method_to_interface: HashMap<Identifier, Identifier>,
    // map from interface name to list of implementations
    pub interface_impls: BTreeMap<Identifier, Vec<InterfaceImpl>>,

    // ADDITIONAL CONSTRAINTS
    // map from types to interfaces they have been constrained to
    pub types_constrained_to_interfaces: BTreeMap<Type, Vec<(Identifier, Prov)>>,

    // ERRORS

    // unbound variables
    pub unbound_vars: BTreeSet<ast::Id>,
    pub unbound_interfaces: BTreeSet<ast::Id>,
    // multiple definitions
    pub multiple_adt_defs: BTreeMap<Identifier, Vec<ast::Id>>,
    pub multiple_interface_defs: BTreeMap<Identifier, Vec<ast::Id>>,
    // interface implementations
    pub multiple_interface_impls: BTreeMap<Identifier, Vec<ast::Id>>,
    pub interface_impl_for_instantiated_adt: Vec<ast::Id>,
    // non-exhaustive matches
    pub nonexhaustive_matches: BTreeMap<ast::Id, Vec<DeconstructedPat>>,
    pub redundant_matches: BTreeMap<ast::Id, Vec<ast::Id>>,
}

impl InferenceContext {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn adt_def_of_variant(&self, variant: &Identifier) -> Option<AdtDef> {
        let adt_name = self.variants_to_adt.get(variant)?;
        self.adt_defs.get(adt_name).cloned()
    }

    pub fn interface_def_of_ident(&self, ident: &Identifier) -> Option<InterfaceDef> {
        self.interface_defs.get(ident).cloned()
    }

    pub fn variants_of_adt(&self, adt: &Identifier) -> Vec<Identifier> {
        self.adt_defs
            .get(adt)
            .unwrap()
            .variants
            .iter()
            .map(|v| v.ctor.clone())
            .collect()
    }
}

impl UnifVarData {
    fn empty() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    fn extend(&mut self, t_other: Type) {
        let key = t_other.key().unwrap();

        // accumulate provenances and constrain children to each other if applicable
        if let Some(t) = self.types.get_mut(&key) {
            match &t_other {
                Type::UnifVar(_) => panic!("should not be Type::UnifVar"),
                Type::Unit(other_provs)
                | Type::Int(other_provs)
                | Type::Float(other_provs)
                | Type::Bool(other_provs)
                | Type::String(other_provs) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                }
                Type::Poly(other_provs, _, _interfaces) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                }
                Type::Function(other_provs, args1, out1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let Type::Function(_, args2, out2) = t {
                        for (arg, arg2) in args1.iter().zip(args2.iter()) {
                            constrain(arg.clone(), arg2.clone());
                        }
                        constrain(*out1.clone(), *out2.clone());
                    }
                }
                Type::Tuple(other_provs, elems1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let Type::Tuple(_, elems2) = t {
                        for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                            constrain(elem.clone(), elem2.clone());
                        }
                    }
                }
                Type::AdtInstance(other_provs, _, other_tys) => {
                    if let Type::AdtInstance(_, _, tys) = t {
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

    fn merge(first: Self, second: Self) -> Self {
        let mut merged_types = Self { types: first.types };
        for (_key, t) in second.types {
            merged_types.extend(t);
        }
        merged_types
    }
}

fn constrain(expected: Type, actual: Type) {
    match (expected, actual) {
        (Type::UnifVar(ref mut tvar), Type::UnifVar(ref mut tvar2)) => {
            tvar.union_with(tvar2, UnifVarData::merge);
        }
        (t, Type::UnifVar(tvar)) | (Type::UnifVar(tvar), t) => {
            let mut data = tvar.clone_data();
            data.extend(t);
            tvar.replace_data(data);
        }
        _ => {}
    }
}

pub struct Gamma {
    pub vars: HashMap<Identifier, Type>,
    poly_type_vars: HashSet<Identifier>,
    enclosing: Option<Rc<RefCell<Gamma>>>,
}

pub fn make_new_gamma() -> Rc<RefCell<Gamma>> {
    let gamma = Gamma::empty();
    gamma.borrow_mut().extend(
        &String::from("newline"),
        Type::String(RefCell::new(BTreeSet::new())),
    );
    gamma.borrow_mut().extend(
        &String::from("print_string"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_string(Prov::FuncArg(
                Box::new(Prov::Builtin("print_string: string -> void".to_string())),
                0,
            ))],
            Type::make_unit(Prov::FuncOut(Box::new(Prov::Builtin(
                "print_string: string -> void".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("equals_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(
                    Box::new(Prov::Builtin("equals_int: (int, int) -> bool".to_string())),
                    0,
                )),
                Type::make_int(Prov::FuncArg(
                    Box::new(Prov::Builtin("equals_int: (int, int) -> bool".to_string())),
                    1,
                )),
            ],
            Type::make_bool(Prov::FuncOut(Box::new(Prov::Builtin(
                "equals_int: (int, int) -> bool".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("equals_string"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "equals_string: (string, string) -> bool".to_string(),
                    )),
                    0,
                )),
                Type::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "equals_string: (string, string) -> bool".to_string(),
                    )),
                    1,
                )),
            ],
            Type::make_bool(Prov::FuncOut(Box::new(Prov::Builtin(
                "equals_string: (string, string) -> bool".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("int_to_string"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_int(Prov::FuncArg(
                Box::new(Prov::Builtin("int_to_string: int -> string".to_string())),
                0,
            ))],
            Type::make_string(Prov::FuncOut(Box::new(Prov::Builtin(
                "int_to_string: int -> string".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("float_to_string"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_float(Prov::FuncArg(
                Box::new(Prov::Builtin(
                    "float_to_string: float -> string".to_string(),
                )),
                0,
            ))],
            Type::make_string(Prov::FuncOut(Box::new(Prov::Builtin(
                "float_to_string: float -> string".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("to_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_int(Prov::FuncArg(
                Box::new(Prov::Builtin("to_float: int -> float".to_string())),
                0,
            ))],
            Type::make_float(Prov::FuncOut(Box::new(Prov::Builtin(
                "to_float: int -> float".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("round"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_float(Prov::FuncArg(
                Box::new(Prov::Builtin("round: float -> int".to_string())),
                0,
            ))],
            Type::make_int(Prov::FuncOut(Box::new(Prov::Builtin(
                "round: float -> int".to_string(),
            ))))
            .into(),
        ),
    );
    gamma.borrow_mut().extend(
        &String::from("append_strings"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "append_strings: (string, string) -> string".to_string(),
                    )),
                    0,
                )),
                Type::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin(
                        "append_strings: (string, string) -> string".to_string(),
                    )),
                    1,
                )),
            ],
            Type::make_string(Prov::FuncOut(Box::new(Prov::Builtin(
                "append_strings: (string, string) -> string".to_string(),
            ))))
            .into(),
        ),
    );
    let prov = Prov::Builtin("add_int: (int, int) -> int".to_string());
    gamma.borrow_mut().extend(
        &String::from("add_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_int(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("minus_int: (int, int) -> int".to_string());
    gamma.borrow_mut().extend(
        &String::from("minus_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_int(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("multiply_int: (int, int) -> int".to_string());
    gamma.borrow_mut().extend(
        &String::from("multiply_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_int(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("divide_int: (int, int) -> int".to_string());
    gamma.borrow_mut().extend(
        &String::from("divide_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_int(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("pow_int: (int, int) -> int".to_string());
    gamma.borrow_mut().extend(
        &String::from("pow_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_int(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("less_than_int: (int, int) -> bool".to_string());
    gamma.borrow_mut().extend(
        &String::from("less_than_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_int(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_int(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_bool(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("add_float: (float, float) -> float".to_string());
    gamma.borrow_mut().extend(
        &String::from("add_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_float(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("minus_float: (float, float) -> float".to_string());
    gamma.borrow_mut().extend(
        &String::from("minus_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_float(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("multiply_float: (float, float) -> float".to_string());
    gamma.borrow_mut().extend(
        &String::from("multiply_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_float(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("divide_float: (float, float) -> float".to_string());
    gamma.borrow_mut().extend(
        &String::from("divide_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_float(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("pow_float: (float, float) -> float".to_string());
    gamma.borrow_mut().extend(
        &String::from("pow_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_float(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("sqrt_float: (float) -> float".to_string());
    gamma.borrow_mut().extend(
        &String::from("sqrt_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_float(Prov::FuncArg(prov.clone().into(), 0))],
            Type::make_float(Prov::FuncOut(prov.into())).into(),
        ),
    );
    let prov = Prov::Builtin("less_than_float: (float, float) -> bool".to_string());
    gamma.borrow_mut().extend(
        &String::from("less_than_float"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![
                Type::make_float(Prov::FuncArg(prov.clone().into(), 0)),
                Type::make_float(Prov::FuncArg(prov.clone().into(), 1)),
            ],
            Type::make_bool(Prov::FuncOut(prov.into())).into(),
        ),
    );
    gamma
}

impl fmt::Display for Gamma {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:#?})\n", Gamma::debug_helper(self))
    }
}

impl Gamma {
    pub fn debug_helper(&self) -> Vec<String> {
        let mut current = Vec::new();
        for (key, value) in &self.vars {
            current.push(format!("{}: {}", key.clone(), value.clone()))
        }
        match &self.enclosing {
            Some(env) => {
                let mut all = env.borrow_mut().debug_helper();
                all.append(&mut current);
                all
            }
            None => current,
        }
    }

    pub fn empty() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            vars: HashMap::new(),
            poly_type_vars: HashSet::new(),
            enclosing: None,
        }))
    }

    pub fn new(enclosing: Option<Rc<RefCell<Gamma>>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            vars: HashMap::new(),
            poly_type_vars: HashSet::new(),
            enclosing,
        }))
    }

    pub fn lookup(&self, id: &Identifier) -> Option<Type> {
        match self.vars.get(id) {
            Some(typ) => Some(typ.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, id: &Identifier, typ: Type) {
        self.vars.insert(id.clone(), typ);
    }

    pub fn add_polys(&mut self, ty: &Type) {
        match ty {
            Type::Poly(_, ident, _interfaces) => {
                self.poly_type_vars.insert(ident.clone());
            }
            Type::AdtInstance(_, _, params) => {
                for param in params {
                    self.add_polys(param);
                }
            }
            // TODO: need this??
            // Type::UnifVar(tvar) => {
            //     let data = tvar.clone_data();
            //     for (_, ty) in data.types {
            //         self.extend_poly(&ty);
            //     }
            // }
            Type::Function(_, args, out) => {
                for arg in args {
                    self.add_polys(arg);
                }
                self.add_polys(out);
            }
            Type::Tuple(_, elems) => {
                for elem in elems {
                    self.add_polys(elem);
                }
            }
            _ => {}
        }
    }

    pub fn lookup_poly(&self, id: &Identifier) -> bool {
        match self.poly_type_vars.get(id) {
            Some(_) => true,
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup_poly(id),
                None => false,
            },
        }
    }
}

#[derive(Debug, Clone)]
pub enum Mode {
    Syn,
    Ana { expected: Type },
}

pub fn generate_constraints_expr(
    gamma: Rc<RefCell<Gamma>>,
    mode: Mode,
    expr: Rc<Expr>,
    inf_ctx: &mut InferenceContext,
) {
    let node_ty = Type::from_node(inf_ctx, expr.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(expected, node_ty.clone()),
    };
    match &*expr.exprkind {
        ExprKind::Unit => {
            constrain(node_ty, Type::make_unit(Prov::Node(expr.id)));
        }
        ExprKind::Int(_) => {
            constrain(node_ty, Type::make_int(Prov::Node(expr.id)));
        }
        ExprKind::Float(_) => {
            constrain(node_ty, Type::make_float(Prov::Node(expr.id)));
        }
        ExprKind::Bool(_) => {
            constrain(node_ty, Type::make_bool(Prov::Node(expr.id)));
        }
        ExprKind::Str(_) => {
            constrain(node_ty, Type::make_string(Prov::Node(expr.id)));
        }
        ExprKind::List(exprs) => {
            let elem_ty = Type::fresh_unifvar(inf_ctx, Prov::ListElem(Prov::Node(expr.id).into()));
            constrain(
                node_ty,
                Type::make_def_instance(
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
        ExprKind::Var(id) => {
            let lookup = gamma.borrow_mut().lookup(id);
            if let Some(typ) = lookup {
                // replace polymorphic types with unifvars if necessary
                let typ = typ.instantiate(gamma, inf_ctx, Prov::Node(expr.id));
                constrain(typ, node_ty);
                return;
            }
            let adt_def = inf_ctx.adt_def_of_variant(id);
            if let Some(adt_def) = adt_def {
                let nparams = adt_def.params.len();
                let mut params = vec![];
                let mut substitution = BTreeMap::new();
                for i in 0..nparams {
                    params.push(Type::fresh_unifvar(
                        inf_ctx,
                        Prov::InstantiateAdtParam(Box::new(Prov::Node(expr.id)), i as u8),
                    ));
                    substitution.insert(adt_def.params[i].clone(), params[i].clone());
                }
                let def_type = Type::make_def_instance(
                    Prov::AdtDef(Box::new(Prov::Node(expr.id))),
                    adt_def.name,
                    params,
                );

                let the_variant = adt_def.variants.iter().find(|v| v.ctor == *id).unwrap();
                if let Type::Unit(_) = the_variant.data {
                    constrain(node_ty, def_type);
                } else if let Type::Tuple(_, elems) = &the_variant.data {
                    let args = elems
                        .iter()
                        .map(|e| {
                            e.clone().subst(
                                gamma.clone(),
                                inf_ctx,
                                Prov::Node(expr.id),
                                &substitution,
                            )
                        })
                        .collect();
                    constrain(
                        node_ty,
                        Type::make_arrow(args, def_type, Prov::Node(expr.id)),
                    );
                } else {
                    constrain(
                        node_ty,
                        Type::make_arrow(
                            vec![the_variant.data.clone().subst(
                                gamma,
                                inf_ctx,
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
                constrain(node_ty, Type::make_unit(Prov::Node(expr.id)));
                return;
            }
            let new_gamma = Gamma::new(Some(gamma));
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
                    new_gamma.clone(),
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                    inf_ctx,
                    true,
                );
                constrain(node_ty, Type::make_unit(Prov::Node(expr.id)))
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: Type::make_bool(Prov::Node(cond.id)),
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
                            expected: Type::make_unit(Prov::Node(expr.id)),
                        },
                        expr1.clone(),
                        inf_ctx,
                    );
                    constrain(node_ty, Type::make_unit(Prov::Node(expr.id)))
                }
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: Type::make_bool(Prov::Node(cond.id)),
                },
                cond.clone(),
                inf_ctx,
            );
            generate_constraints_expr(gamma, Mode::Syn, expr.clone(), inf_ctx);
            constrain(node_ty, Type::make_unit(Prov::Node(expr.id)))
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = Type::from_node(inf_ctx, scrut.id);
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: ty_scrutiny.clone(),
                },
                scrut.clone(),
                inf_ctx,
            );
            for arm in arms {
                let new_gamma = Gamma::new(Some(gamma.clone()));
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
            let body_gamma = Gamma::new(Some(gamma));

            // arguments
            let ty_args = args
                .iter()
                .map(|(arg, arg_annot)| {
                    let ty_pat = Type::from_node(inf_ctx, arg.id);
                    match arg_annot {
                        Some(arg_annot) => {
                            let ty_annot = Type::from_node(inf_ctx, arg_annot.id());
                            let arg_annot = ast_type_to_statics_type(inf_ctx, arg_annot.clone());
                            constrain(ty_annot.clone(), arg_annot.clone());
                            body_gamma.borrow_mut().add_polys(&arg_annot);
                            generate_constraints_pat(
                                body_gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                                Mode::Ana { expected: ty_annot },
                                arg.clone(),
                                inf_ctx,
                            )
                        }
                        None => generate_constraints_pat(
                            body_gamma.clone(),
                            Mode::Syn,
                            arg.clone(),
                            inf_ctx,
                        ),
                    }
                    ty_pat
                })
                .collect();

            // body
            let ty_body =
                Type::fresh_unifvar(inf_ctx, Prov::FuncOut(Box::new(Prov::Node(func_node_id))));
            generate_constraints_expr(
                body_gamma.clone(),
                Mode::Ana {
                    expected: ty_body.clone(),
                },
                body.clone(),
                inf_ctx,
            );
            if let Some(out_annot) = out_annot {
                let out_annot = ast_type_to_statics_type(inf_ctx, out_annot.clone());
                body_gamma.borrow_mut().add_polys(&out_annot);
                generate_constraints_expr(
                    body_gamma,
                    Mode::Ana {
                        expected: out_annot,
                    },
                    body.clone(),
                    inf_ctx,
                );
            }

            let ty_func = Type::make_arrow(ty_args, ty_body, Prov::Node(func_node_id));

            constrain(ty_func, node_ty);
        }
        ExprKind::FuncAp(func, args) => {
            // arguments
            let tys_args: Vec<Type> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = Type::fresh_unifvar(
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
            let ty_body =
                Type::fresh_unifvar(inf_ctx, Prov::FuncOut(Box::new(Prov::Node(func.id))));
            constrain(ty_body.clone(), node_ty);

            // function type
            let ty_func = Type::make_arrow(tys_args, ty_body, Prov::Node(expr.id));
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
                .map(|expr| Type::fresh_unifvar(inf_ctx, Prov::Node(expr.id)))
                .collect();
            constrain(Type::make_tuple(tys, Prov::Node(expr.id)), node_ty);
            for expr in exprs {
                generate_constraints_expr(gamma.clone(), Mode::Syn, expr.clone(), inf_ctx);
            }
        }
    }
}

pub fn generate_constraints_stmt(
    gamma: Rc<RefCell<Gamma>>,
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
                            inf_ctx,
                            Prov::Node(stmt.id),
                            &substitution,
                        );

                        constrain(expected, Type::from_node(inf_ctx, pat.id));

                        generate_constraints_stmt(
                            gamma.clone(),
                            Mode::Syn,
                            statement.clone(),
                            inf_ctx,
                            false,
                        );
                    } else {
                        // TODO: emit error interface doesn't have method
                    }
                }
            } else {
                inf_ctx.unbound_interfaces.insert(stmt.id);
            }
        }
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(ident, ty) => {
                let left = Type::fresh_unifvar(inf_ctx, Prov::Alias(ident.clone()));
                let right = ast_type_to_statics_type(inf_ctx, ty.clone());
                constrain(left, right);
            }
            TypeDefKind::Adt(..) => {}
        },
        StmtKind::Expr(expr) => {
            generate_constraints_expr(gamma, mode, expr.clone(), inf_ctx);
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            let ty_pat = Type::from_node(inf_ctx, pat.id);

            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                inf_ctx,
            );

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_statics_type(inf_ctx, ty_ann.clone());
                gamma.borrow_mut().add_polys(&ty_ann);
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
        StmtKind::Set(pat, expr) => {
            let ty_pat: Type = Type::from_node(inf_ctx, pat.id);
            generate_constraints_expr(
                gamma.clone(),
                Mode::Ana {
                    expected: ty_pat.clone(),
                },
                expr.clone(),
                inf_ctx,
            );

            let ty_expr = Type::from_node(inf_ctx, expr.id);

            constrain(ty_pat, ty_expr);
        }
        StmtKind::FuncDef(name, args, out_annot, body) => {
            let func_node_id = stmt.id;

            let ty_pat = Type::from_node(inf_ctx, name.id);
            if add_to_gamma {
                gamma
                    .borrow_mut()
                    .extend(&name.patkind.get_identifier_of_variable(), ty_pat.clone());
            }

            let body_gamma = Gamma::new(Some(gamma));

            // BEGIN TODO use helper function for functions again

            // arguments
            let ty_args = args
                .iter()
                .map(|(arg, arg_annot)| {
                    let ty_pat = Type::from_node(inf_ctx, arg.id);
                    match arg_annot {
                        Some(arg_annot) => {
                            let ty_annot = Type::from_node(inf_ctx, arg_annot.id());
                            let arg_annot = ast_type_to_statics_type(inf_ctx, arg_annot.clone());
                            constrain(ty_annot.clone(), arg_annot.clone());
                            body_gamma.borrow_mut().add_polys(&arg_annot);
                            generate_constraints_pat(
                                body_gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                                Mode::Ana { expected: ty_annot },
                                arg.clone(),
                                inf_ctx,
                            )
                        }
                        None => generate_constraints_pat(
                            body_gamma.clone(),
                            Mode::Syn,
                            arg.clone(),
                            inf_ctx,
                        ),
                    }
                    ty_pat
                })
                .collect();

            // body
            let ty_body =
                Type::fresh_unifvar(inf_ctx, Prov::FuncOut(Box::new(Prov::Node(func_node_id))));
            generate_constraints_expr(
                body_gamma.clone(),
                Mode::Ana {
                    expected: ty_body.clone(),
                },
                body.clone(),
                inf_ctx,
            );
            if let Some(out_annot) = out_annot {
                let out_annot = ast_type_to_statics_type(inf_ctx, out_annot.clone());
                body_gamma.borrow_mut().add_polys(&out_annot);
                generate_constraints_expr(
                    body_gamma,
                    Mode::Ana {
                        expected: out_annot,
                    },
                    body.clone(),
                    inf_ctx,
                );
            }

            let ty_func = Type::make_arrow(ty_args, ty_body, Prov::Node(func_node_id));
            // END TODO use helper function for functions again

            constrain(ty_pat, ty_func);
        }
    }
}

pub fn generate_constraints_pat(
    gamma: Rc<RefCell<Gamma>>,
    mode: Mode,
    pat: Rc<Pat>,
    inf_ctx: &mut InferenceContext,
) {
    let ty_pat = Type::from_node(inf_ctx, pat.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(expected, ty_pat.clone()),
    };
    match &*pat.patkind {
        PatKind::Wildcard => (),
        PatKind::Unit => {
            constrain(ty_pat, Type::make_unit(Prov::Node(pat.id)));
        }
        PatKind::Int(_) => {
            constrain(ty_pat, Type::make_int(Prov::Node(pat.id)));
        }
        PatKind::Float(_) => {
            constrain(ty_pat, Type::make_float(Prov::Node(pat.id)));
        }
        PatKind::Bool(_) => {
            constrain(ty_pat, Type::make_bool(Prov::Node(pat.id)));
        }
        PatKind::Str(_) => {
            constrain(ty_pat, Type::make_string(Prov::Node(pat.id)));
        }
        PatKind::Var(identifier) => {
            // letrec: extend context with id and type before analyzing against said type
            gamma.borrow_mut().extend(identifier, ty_pat);
        }
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => Type::from_node(inf_ctx, data.id),
                None => Type::make_unit(Prov::VariantNoData(Box::new(Prov::Node(pat.id)))),
            };
            let mut substitution = BTreeMap::new();
            let ty_adt_instance = {
                let adt_def = inf_ctx.adt_def_of_variant(tag);

                if let Some(adt_def) = adt_def {
                    let nparams = adt_def.params.len();
                    let mut params = vec![];
                    for i in 0..nparams {
                        params.push(Type::fresh_unifvar(
                            inf_ctx,
                            Prov::InstantiateAdtParam(Box::new(Prov::Node(pat.id)), i as u8),
                        ));
                        substitution.insert(adt_def.params[i].clone(), params[i].clone());
                    }
                    let def_type = Type::make_def_instance(
                        Prov::AdtDef(Box::new(Prov::Node(pat.id))),
                        adt_def.name,
                        params,
                    );

                    let variant_def = adt_def.variants.iter().find(|v| v.ctor == *tag).unwrap();
                    let variant_data_ty = variant_def.data.clone().subst(
                        gamma.clone(),
                        inf_ctx,
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
                .map(|pat| Type::fresh_unifvar(inf_ctx, Prov::Node(pat.id)))
                .collect();
            constrain(Type::make_tuple(tys_elements, Prov::Node(pat.id)), ty_pat);
            for pat in pats {
                generate_constraints_pat(gamma.clone(), Mode::Syn, pat.clone(), inf_ctx)
            }
        }
    }
}

pub fn gather_definitions_stmt(
    inf_ctx: &mut InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    stmt: Rc<ast::Stmt>,
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
                let node_ty = Type::from_node(inf_ctx, p.id());
                constrain(node_ty.clone(), ty_annot.clone());
                methods.push(InterfaceDefMethod {
                    name: p.ident.clone(),
                    ty: node_ty.clone(),
                });
                inf_ctx
                    .method_to_interface
                    .insert(p.ident.clone(), ident.clone());
                gamma.borrow_mut().extend(&p.ident, node_ty);
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
                    let entry = inf_ctx.multiple_adt_defs.entry(ident.clone()).or_default();
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
                            Type::make_unit(Prov::VariantNoData(Box::new(Prov::Node(v.id))))
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
                    let ast::TypeKind::Poly(ident, _) = &*p.typekind else {
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
        },
        StmtKind::Expr(_) => {}
        StmtKind::Let(..) => {}
        StmtKind::FuncDef(name, _args, _out_annot, _body) => {
            inf_ctx
                .fun_defs
                .insert(name.patkind.get_identifier_of_variable(), stmt.clone());
            gamma.borrow_mut().extend(
                &name.patkind.get_identifier_of_variable(),
                Type::from_node(inf_ctx, name.id),
            );
        }
        StmtKind::Set(..) => {}
    }
}

fn monomorphized_ty_to_builtin_ty(ty: TypeMonomorphized, prov_builtin: Prov) -> Type {
    match ty {
        TypeMonomorphized::Unit => Type::make_unit(prov_builtin),
        TypeMonomorphized::Int => Type::make_int(prov_builtin),
        TypeMonomorphized::Float => Type::make_float(prov_builtin),
        TypeMonomorphized::Bool => Type::make_bool(prov_builtin),
        TypeMonomorphized::String => Type::make_string(prov_builtin),
        TypeMonomorphized::Tuple(elements) => {
            let elements = elements
                .into_iter()
                .map(|e| monomorphized_ty_to_builtin_ty(e, prov_builtin.clone()))
                .collect();
            Type::make_tuple(elements, prov_builtin)
        }
        TypeMonomorphized::Function(args, out) => {
            let args = args
                .into_iter()
                .map(|a| monomorphized_ty_to_builtin_ty(a, prov_builtin.clone()))
                .collect();
            let out = monomorphized_ty_to_builtin_ty(*out, prov_builtin.clone());
            Type::make_arrow(args, out, prov_builtin.clone())
        }
        TypeMonomorphized::Adt(name, params) => {
            let params = params
                .into_iter()
                .map(|p| monomorphized_ty_to_builtin_ty(p, prov_builtin.clone()))
                .collect();
            Type::make_def_instance(prov_builtin, name, params)
        }
    }
}

pub fn gather_definitions_toplevel<Effect: crate::side_effects::EffectTrait>(
    inf_ctx: &mut InferenceContext,
    gamma: Rc<RefCell<Gamma>>,
    toplevel: Rc<ast::Toplevel>,
) {
    for eff in Effect::enumerate().iter() {
        let provs = RefCell::new(BTreeSet::new());
        let prov = Prov::Builtin(format!(
            "{}: {:#?}",
            eff.function_name(),
            eff.type_signature()
        ));
        provs.borrow_mut().insert(prov.clone());
        let mut args = Vec::new();
        for arg in eff.type_signature().0 {
            args.push(monomorphized_ty_to_builtin_ty(arg, prov.clone()));
        }
        let typ = Type::Function(
            provs,
            args,
            monomorphized_ty_to_builtin_ty(eff.type_signature().1, prov).into(),
        );
        gamma.borrow_mut().extend(&eff.function_name(), typ)
    }
    for statement in toplevel.statements.iter() {
        gather_definitions_stmt(inf_ctx, gamma.clone(), statement.clone());
    }
}

pub fn generate_constraints_toplevel(
    gamma: Rc<RefCell<Gamma>>,
    toplevel: Rc<ast::Toplevel>,
    inf_ctx: &mut InferenceContext,
) -> Rc<RefCell<Gamma>> {
    for statement in toplevel.statements.iter() {
        generate_constraints_stmt(gamma.clone(), Mode::Syn, statement.clone(), inf_ctx, true);
    }
    gamma
}

// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub fn result_of_constraint_solving(
    inf_ctx: &mut InferenceContext,
    _tyctx: Rc<RefCell<Gamma>>,
    node_map: &ast::NodeMap,
    sources: &ast::Sources,
) -> Result<(), String> {
    // get list of type conflicts
    let mut type_conflicts = Vec::new();
    for potential_types in inf_ctx.vars.values() {
        let type_suggestions = potential_types.clone_data().types;
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions.clone());
        }
    }

    // replace underdetermined types with unit
    if type_conflicts.is_empty() {
        for potential_types in inf_ctx.vars.values() {
            let mut data = potential_types.clone_data();
            let suggestions = &mut data.types;
            if suggestions.is_empty() {
                suggestions.insert(
                    TypeKey::Unit,
                    Type::make_unit(Prov::UnderdeterminedCoerceToUnit),
                );
                potential_types.replace_data(data);
            }
        }
    }

    // look for error of multiple interface implementations for the same type
    for (ident, impls) in inf_ctx.interface_impls.iter() {
        // map from implementation type to location
        // TODO: key is mutable. Can TypeKey or TypeMonomorphic be used instead? If not, create a TypeImmutable datatype
        let mut impls_by_type: BTreeMap<Type, Vec<ast::Id>> = BTreeMap::new();
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
            if let Type::Poly(_, _, interfaces2) = &typ {
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
                let _ = write!(
                    err_string,
                    "error: the interface '{}' is not implemented for type '{}'\n",
                    interface, typ
                );
                if let Some(id) = prov.get_location() {
                    let span = node_map.get(&id).unwrap().span();
                    err_string.push_str(&span.display(sources, ""));
                }
            }
        }
    }

    if inf_ctx.unbound_vars.is_empty()
        && inf_ctx.unbound_interfaces.is_empty()
        && type_conflicts.is_empty()
        && inf_ctx.multiple_adt_defs.is_empty()
        && inf_ctx.multiple_interface_defs.is_empty()
        && inf_ctx.multiple_interface_impls.is_empty()
        && inf_ctx.interface_impl_for_instantiated_adt.is_empty()
        && !bad_instantiations
    {
        for (node_id, node) in node_map.iter() {
            let ty = Type::solution_of_node(inf_ctx, *node_id);
            let _span = node.span();
            if let Some(_ty) = ty {}
        }
        return Ok(());
    }

    if !inf_ctx.unbound_vars.is_empty() {
        err_string.push_str("You have unbound variables!\n");
        for ast_id in inf_ctx.unbound_vars.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            err_string.push_str(&span.display(sources, ""));
        }
    }
    if !inf_ctx.unbound_interfaces.is_empty() {
        for ast_id in inf_ctx.unbound_interfaces.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            err_string
                .push_str(&span.display(sources, "Interface being implemented is not defined\n"));
        }
    }
    if !inf_ctx.multiple_adt_defs.is_empty() {
        for (ident, adt_ids) in inf_ctx.multiple_adt_defs.iter() {
            let _ = writeln!(err_string, "Multiple definitions for type {}, ident", ident);
            for ast_id in adt_ids {
                let span = node_map.get(ast_id).unwrap().span();
                err_string.push_str(&span.display(sources, ""));
            }
        }
    }
    if !inf_ctx.multiple_interface_defs.is_empty() {
        for (ident, interface_ids) in inf_ctx.multiple_interface_defs.iter() {
            let _ = writeln!(err_string, "Multiple definitions for interface {}", ident);
            for ast_id in interface_ids {
                let span = node_map.get(ast_id).unwrap().span();
                err_string.push_str(&span.display(sources, ""));
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
                err_string.push_str(&span.display(sources, ""));
            }
        }
    }

    if !inf_ctx.interface_impl_for_instantiated_adt.is_empty() {
        for ast_id in inf_ctx.interface_impl_for_instantiated_adt.iter() {
            let span = node_map.get(ast_id).unwrap().span();
            err_string.push_str(&span.display(
                sources,
                "Interface implementations for instantiated ADTs are not supported.\n",
            ));
        }
    }

    if !type_conflicts.is_empty() {
        let mut type_conflicts = type_conflicts
            .iter()
            .map(|type_suggestions| {
                let mut types_sorted: Vec<_> = type_suggestions.values().collect();
                types_sorted.sort_by_key(|ty| ty.provs().borrow().len());
                types_sorted
            })
            .collect::<Vec<_>>();
        type_conflicts.sort();
        for type_conflict in type_conflicts {
            err_string.push_str("Conflicting types: ");
            fmt_conflicting_types(&type_conflict, &mut err_string).unwrap();
            writeln!(err_string).unwrap();
            for ty in type_conflict {
                err_string.push('\n');
                match &ty {
                    Type::UnifVar(_) => err_string.push_str("Sources of unknown:\n"), // idk about this
                    Type::Poly(_, _, _) => err_string.push_str("Sources of generic type:\n"),
                    Type::AdtInstance(_, ident, params) => {
                        let _ = write!(err_string, "Sources of type {}<", ident);
                        for (i, param) in params.iter().enumerate() {
                            if i != 0 {
                                err_string.push_str(", ");
                            }
                            let _ = writeln!(err_string, "{param}");
                        }
                        err_string.push_str(">\n");
                    }
                    Type::Unit(_) => err_string.push_str("Sources of void:\n"),
                    Type::Int(_) => err_string.push_str("Sources of int:\n"),
                    Type::Float(_) => err_string.push_str("Sources of float:\n"),
                    Type::Bool(_) => err_string.push_str("Sources of bool:\n"),
                    Type::String(_) => err_string.push_str("Sources of string:\n"),
                    Type::Function(_, args, _) => {
                        let _ = writeln!(
                            err_string,
                            "Sources of function with {} arguments",
                            args.len()
                        );
                    }
                    Type::Tuple(_, elems) => {
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
                    Prov::AdtDef(_) => 8,
                    Prov::InstantiateAdtParam(_, _) => 9,
                    Prov::ListElem(_) => 10,
                    Prov::BinopLeft(_) => 11,
                    Prov::BinopRight(_) => 12,
                    Prov::UnderdeterminedCoerceToUnit => 13,
                });
                for cause in provs_vec {
                    match cause {
                        Prov::Builtin(s) => {
                            let _ = writeln!(err_string, "The builtin function {s}");
                        }
                        Prov::Node(id) => {
                            let span = node_map.get(id).unwrap().span();
                            err_string.push_str(&span.display(sources, ""));
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
                                    err_string.push_str(&span.display(
                                        sources,
                                        &format!("The #{n} argument of this function"),
                                    ));
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
                                err_string.push_str(
                                    &span.display(sources, "The output of this function"),
                                );
                            }
                            _ => unreachable!(),
                        },
                        Prov::BinopLeft(inner) => {
                            err_string.push_str("The left operand of operator\n");
                            if let Prov::Node(id) = **inner {
                                let span = node_map.get(&id).unwrap().span();
                                err_string.push_str(&span.display(sources, ""));
                            }
                        }
                        Prov::BinopRight(inner) => {
                            err_string.push_str("The left operand of this operator\n");
                            if let Prov::Node(id) = **inner {
                                let span = node_map.get(&id).unwrap().span();
                                err_string.push_str(&span.display(sources, ""));
                            }
                        }
                        Prov::ListElem(_) => {
                            err_string.push_str("The element of some list");
                        }
                        Prov::Alias(ident) => {
                            let _ = writeln!(err_string, "The type alias {ident}");
                        }
                        Prov::AdtDef(_prov) => {
                            err_string.push_str("Some ADT definition");
                        }
                        Prov::InstantiateAdtParam(_, _) => {
                            err_string.push_str("Some instance of an Adt's variant");
                        }
                        Prov::VariantNoData(_prov) => {
                            err_string.push_str("The data of some ADT variant");
                        }
                    }
                }
            }
            writeln!(err_string).unwrap();
        }
    }

    Err(err_string)
}

pub fn result_of_additional_analysis(
    inf_ctx: &mut InferenceContext,
    toplevels: &[Rc<ast::Toplevel>],
    node_map: &ast::NodeMap,
    sources: &ast::Sources,
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
        err_string.push_str(&span.display(
            sources,
            "This match expression doesn't cover every possibility:\n",
        ));
        err_string.push_str("\nThe following cases are missing:\n");
        for pat in missing_pattern_suggestions {
            let _ = writeln!(err_string, "\t`{pat}`\n");
        }
    }

    for (match_expr, redundant_pattern_suggestions) in inf_ctx.redundant_matches.iter() {
        let span = node_map.get(match_expr).unwrap().span();
        err_string.push_str(&span.display(sources, "This match expression has redundant cases:\n"));
        err_string.push_str("\nTry removing these cases\n");
        for pat in redundant_pattern_suggestions {
            let span = node_map.get(pat).unwrap().span();
            err_string.push_str(&span.display(sources, ""));
        }
    }

    Err(err_string)
}

fn check_pattern_exhaustiveness_toplevel(inf_ctx: &mut InferenceContext, toplevel: &ast::Toplevel) {
    for statement in toplevel.statements.iter() {
        check_pattern_exhaustiveness_stmt(inf_ctx, statement);
    }
}

fn check_pattern_exhaustiveness_stmt(inf_ctx: &mut InferenceContext, stmt: &ast::Stmt) {
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

fn check_pattern_exhaustiveness_expr(inf_ctx: &mut InferenceContext, expr: &ast::Expr) {
    match &*expr.exprkind {
        ExprKind::Match(..) => match_expr_exhaustive_check(inf_ctx, expr),

        ExprKind::Unit
        | ExprKind::Int(_)
        | ExprKind::Float(_)
        | ExprKind::Bool(_)
        | ExprKind::Str(_)
        | ExprKind::Var(_) => {}
        ExprKind::List(exprs) => {
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
    }
}

pub fn ty_fits_impl_ty(
    ctx: &InferenceContext,
    typ: Type,
    impl_ty: Type,
) -> Result<(), (Type, Type)> {
    match (&typ, &impl_ty) {
        (Type::Int(..), Type::Int(..))
        | (Type::Bool(..), Type::Bool(..))
        | (Type::Float(..), Type::Float(..))
        | (Type::String(..), Type::String(..))
        | (Type::Unit(..), Type::Unit(..)) => Ok(()),
        (Type::Tuple(_, tys1), Type::Tuple(_, tys2)) => {
            if tys1.len() == tys2.len() {
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone())?;
                }
                Ok(())
            } else {
                Err((typ, impl_ty))
            }
        }
        (Type::Function(_, args1, out1), Type::Function(_, args2, out2)) => {
            if args1.len() == args2.len() {
                for (ty1, ty2) in args1.iter().zip(args2.iter()) {
                    ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone())?;
                }
                ty_fits_impl_ty(ctx, *out1.clone(), *out2.clone())
            } else {
                Err((typ, impl_ty))
            }
        }
        (Type::AdtInstance(_, ident1, tys1), Type::AdtInstance(_, ident2, tys2)) => {
            if ident1 == ident2 && tys1.len() == tys2.len() {
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    let Type::Poly(_, _, interfaces) = ty2.clone() else {
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
        (_, Type::Poly(_, _, interfaces)) => {
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
    typ: Type,
    interfaces: BTreeSet<Identifier>,
) -> bool {
    for interface in interfaces {
        if let Type::Poly(_, _, interfaces2) = &typ {
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
    types: Vec<Type>,
}

impl Matrix {
    fn new(inf_ctx: &InferenceContext, scrutinee_ty: Type, arms: &[ast::MatchArm]) -> Self {
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
                Type::Tuple(_, tys) => {
                    new_types.extend(tys.clone());
                }
                Type::Unit(..) => {}
                _ => panic!("expected type for product constructor"),
            },
            Constructor::Variant(ident) => {
                let adt = inf_ctx.adt_def_of_variant(ident).unwrap();
                let variant = adt.variants.iter().find(|v| v.ctor == *ident).unwrap();
                match &variant.data {
                    Type::Unit(..) => {}
                    Type::Bool(..)
                    | Type::Int(..)
                    | Type::String(..)
                    | Type::Float(..)
                    | Type::Function(..)
                    | Type::Tuple(_, _)
                    | Type::AdtInstance(..) => new_types.push(variant.data.clone()),
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
pub struct DeconstructedPat {
    ctor: Constructor,
    fields: Vec<DeconstructedPat>,
    ty: Type,
}

impl DeconstructedPat {
    fn from_ast_pat(inf_ctx: &InferenceContext, pat: Rc<ast::Pat>) -> Self {
        let ty = Type::solution_of_node(inf_ctx, pat.id).unwrap();
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

    fn field_tys(&self, ctor: &Constructor, inf_ctx: &InferenceContext) -> Vec<Type> {
        match &self.ty {
            Type::Int(..)
            | Type::Float(..)
            | Type::String(..)
            | Type::Bool(..)
            | Type::Unit(..)
            | Type::Poly(..)
            | Type::Function(..) => vec![],
            Type::Tuple(_, tys) => tys.clone(),
            Type::AdtInstance(_, _, _) => match ctor {
                Constructor::Variant(ident) => {
                    let adt = inf_ctx.adt_def_of_variant(ident).unwrap();
                    let variant = adt.variants.iter().find(|v| v.ctor == *ident).unwrap();
                    if !matches!(&variant.data, Type::Unit(..)) {
                        vec![variant.data.clone()]
                    } else {
                        vec![]
                    }
                }
                Constructor::Wildcard(_) => {
                    vec![]
                }
                _ => panic!("unexpected constructor"),
            },
            Type::UnifVar(..) => panic!("unexpected type"),
        }
    }

    fn missing_from_ctor(ctor: &Constructor, ty: Type) -> Self {
        let fields = match ty.clone() {
            Type::Tuple(_, tys) | Type::AdtInstance(_, _, tys) => tys
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
    Variant(Identifier),
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

    fn as_variant_identifier(&self) -> Option<Identifier> {
        match self {
            Constructor::Variant(i) => Some(i.clone()),
            _ => None,
        }
    }

    fn arity(&self, matrix_tys: &[Type], inf_ctx: &InferenceContext) -> usize {
        match self {
            Constructor::Bool(..)
            | Constructor::Int(..)
            | Constructor::String(..)
            | Constructor::Float(..)
            | Constructor::Wildcard(..) => 0,
            Constructor::Product => match &matrix_tys[0] {
                Type::Tuple(_, tys) => tys.len(),
                Type::Unit(..) => 0,
                _ => panic!("unexpected type for product constructor: {}", matrix_tys[0]),
            },
            Constructor::Variant(ident) => {
                let adt = inf_ctx.adt_def_of_variant(ident).unwrap();
                let variant = adt.variants.iter().find(|v| v.ctor == *ident).unwrap();
                if !matches!(&variant.data, Type::Unit(..)) {
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

    fn apply_constructor(&mut self, ctor: &Constructor, arity: usize, head_ty: &Type) {
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

    fn apply_missing_constructors(&mut self, missing_ctors: &[Constructor], head_ty: &Type) {
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
    AdtVariants(Vec<Identifier>),
    Product,    // tuples, including unit
    Unlistable, // int, float, string
}

#[derive(Debug, Clone)]
struct SplitConstructorSet {
    pub present_ctors: Vec<Constructor>,
    pub missing_ctors: Vec<Constructor>,
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
                let mut missing_set: HashSet<Identifier> = adt_variants.iter().cloned().collect();
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
fn match_expr_exhaustive_check(inf_ctx: &mut InferenceContext, expr: &ast::Expr) {
    let ExprKind::Match(scrutiny, arms) = &*expr.exprkind else {
        panic!()
    };

    let scrutinee_ty = Type::solution_of_node(inf_ctx, scrutiny.id);
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

fn ctors_for_ty(inf_ctx: &InferenceContext, ty: &Type) -> ConstructorSet {
    match ty.solution().unwrap() {
        Type::Bool(_) => ConstructorSet::Bool,
        Type::AdtInstance(_, ident, _) => {
            let variants = inf_ctx.variants_of_adt(&ident);
            ConstructorSet::AdtVariants(variants)
        }
        Type::Tuple(..) => ConstructorSet::Product,
        Type::Unit(_) => ConstructorSet::Product,
        Type::Int(_) | Type::Float(_) | Type::String(_) | Type::Function(..) => {
            ConstructorSet::Unlistable
        }
        Type::Poly(..) => ConstructorSet::Unlistable,
        Type::UnifVar(..) => panic!("Unexpected type in ctors_for_ty {:#?}", ty),
    }
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Poly(_, ident, interfaces) => {
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
            Type::AdtInstance(_, ident, params) => {
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
            Type::UnifVar(unifvar) => {
                let types = unifvar.clone_data().types;
                match types.len() {
                    0 => write!(f, "?"),
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
            Type::Unit(_) => write!(f, "void"),
            Type::Int(_) => write!(f, "int"),
            Type::Float(_) => write!(f, "float"),
            Type::Bool(_) => write!(f, "bool"),
            Type::String(_) => write!(f, "string"),
            Type::Function(_, args, out) => {
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
            Type::Tuple(_, elems) => {
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

fn fmt_conflicting_types(types: &[&Type], f: &mut dyn Write) -> fmt::Result {
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
