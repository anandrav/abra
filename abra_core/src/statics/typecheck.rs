/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{
    ArgAnnotated, ArgMaybeAnnotated, AstNode, Expr, ExprKind, FileAst, Identifier, ItemKind, Pat,
    PatKind, Stmt, StmtKind, Type as AstType, TypeDefKind, TypeKind,
};
use crate::ast::{BinaryOperator, Item};
use crate::builtin::Builtin;
use crate::environment::Environment;
use core::panic;
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt::{self, Display, Write};
use std::rc::Rc;
use utils::hash::HashMap;

use super::{
    Declaration, EnumDef, Error, FuncDef, InterfaceDecl, Polytype, StaticsContext, StructDef,
};

pub(crate) fn solve_types(ctx: &mut StaticsContext, file_asts: &Vec<Rc<FileAst>>) {
    for file in file_asts {
        generate_constraints_file_decls(file.clone(), ctx);
    }
    for file in file_asts {
        generate_constraints_file_stmts(file.clone(), ctx);
    }
    check_unifvars(ctx);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TypeVar(UnionFindNode<TypeVarData>);

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TypeVarData {
    pub(crate) types: HashMap<TypeKey, PotentialType>,
    // if this flag is true, typevar's "tag" is solved. For instance, it may be solved to int, fn(_) -> _, or tuple(_, _, _)
    //      its children types may or may not be solved
    pub(crate) locked: bool,
    // if this flag is true, the typevar can't be solved due to an unresolved identifier
    pub(crate) missing_info: bool,
}

impl TypeVarData {
    fn new() -> Self {
        Self {
            types: HashMap::default(),
            locked: false,
            missing_info: false,
        }
    }

    fn singleton_solved(potential_type: PotentialType) -> Self {
        let mut types = HashMap::default();
        types.insert(potential_type.key(), potential_type);
        Self {
            types,
            locked: true,
            missing_info: false,
        }
    }

    fn solution(&self) -> Option<SolvedType> {
        if self.types.len() == 1 && !self.missing_info {
            self.types.values().next().unwrap().solution()
        } else {
            None
        }
    }

    fn merge_data(first: Self, second: Self) -> Self {
        let mut merged_types = Self {
            types: first.types,
            locked: false,
            missing_info: first.missing_info || second.missing_info,
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
                PotentialType::Poly(other_provs, _) => t
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
                    let PotentialType::Nominal(_, _, tys) = t else {
                        unreachable!("should be same length")
                    };
                    assert_eq!(tys.len(), other_tys.len());
                    for (ty, other_ty) in tys.iter().zip(other_tys.iter()) {
                        TypeVar::merge(ty.clone(), other_ty.clone());
                    }

                    t.reasons()
                        .borrow_mut()
                        .extend(other_provs.borrow().clone());
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
    Poly(Reasons, PolyDeclaration),
    Unit(Reasons),
    Int(Reasons),
    Float(Reasons),
    Bool(Reasons),
    String(Reasons),
    Function(Reasons, Vec<TypeVar>, TypeVar),
    Tuple(Reasons, Vec<TypeVar>),
    Nominal(Reasons, Nominal, Vec<TypeVar>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PolyDeclaration(Rc<Polytype>);

impl From<PolyDeclaration> for Declaration {
    fn from(value: PolyDeclaration) -> Self {
        Declaration::Polytype(value.0.clone())
    }
}

impl From<&PolyDeclaration> for Declaration {
    fn from(value: &PolyDeclaration) -> Self {
        Declaration::Polytype(value.0.clone())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum SolvedType {
    Poly(Rc<Polytype>), // type name, then list of Interfaces it must match
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(Vec<SolvedType>, Box<SolvedType>),
    Tuple(Vec<SolvedType>),
    Nominal(Nominal, Vec<SolvedType>),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum Nominal {
    Struct(Rc<StructDef>),
    Enum(Rc<EnumDef>),
    Array,
}

impl Nominal {
    pub(crate) fn name(&self) -> &str {
        match self {
            Self::Struct(struct_def) => &struct_def.name.v,
            Self::Enum(enum_def) => &enum_def.name.v,
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
            Self::Poly(polyty) => !polyty.iface_names.is_empty(),
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
pub(crate) enum Monotype {
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
    Poly(PolyDeclaration),
    TyApp(Nominal, u8), // u8 represents the number of type params
    Unit,
    Int,
    Float,
    Bool,
    String,
    Function(u8), // u8 represents the number of arguments
    Tuple(u8),    // u8 represents the number of elements
}

// Provenances are used to give the *unique* identity of a skolem (type to be solved) (UnifVar) in the SolutionMap
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Prov {
    Node(AstNode), // the type of an expression or statement located at NodeId
    InstantiateUdtParam(AstNode, u8),
    InstantiatePoly(AstNode, Rc<Polytype>),
    FuncArg(AstNode, u8), // u8 represents the index of the argument
    FuncOut(AstNode),     // u8 represents how many arguments before this output
    ListElem(AstNode),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Reason {
    // TODO: get rid of Reason::Node if possible, but no rush
    Node(AstNode), // the type of an expression or statement located at NodeId

    Annotation(AstNode),
    Literal(AstNode),
    Builtin(Builtin), // a builtin function or constant, which doesn't exist in the AST
    BinopLeft(AstNode),
    BinopRight(AstNode),
    BinopOut(AstNode),
    IndexAccess,
    VariantNoData(AstNode), // the type of the data of a variant with no data, always Unit.
    WhileLoopBody(AstNode),
    IfWithoutElse(AstNode),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ConstraintReason {
    None, // TODO: get rid of None if possible, but no rush

    BinaryOperandsMustMatch(AstNode),
    IfElseBodies,
    LetStmtAnnotation,
    LetSetLhsRhs,
    MatchScrutinyAndPattern,
    FuncCall(AstNode),
    ReturnValue,
    // bool
    Condition,
    BinaryOperandBool(AstNode),
    // int
    IndexAccess,
}

type Substitution = HashMap<PolyDeclaration, TypeVar>;

impl PotentialType {
    fn key(&self) -> TypeKey {
        match self {
            PotentialType::Poly(_, decl) => TypeKey::Poly(decl.clone()),
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
            Self::Poly(_, decl) => {
                let polyty = &decl.0;
                Some(SolvedType::Poly(polyty.clone()))
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
            Self::Poly(provs, _)
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

    fn make_poly(reason: Reason, decl: PolyDeclaration) -> PotentialType {
        PotentialType::Poly(reasons_singleton(reason), decl)
    }

    fn make_nominal(reason: Reason, nominal: Nominal, params: Vec<TypeVar>) -> PotentialType {
        PotentialType::Nominal(reasons_singleton(reason), nominal, params)
    }
}

impl TypeVar {
    pub(crate) fn solution(&self) -> Option<SolvedType> {
        self.0.with_data(|d| d.solution())
    }

    fn is_underdetermined(&self) -> bool {
        self.0.with_data(|d| d.types.is_empty())
    }

    fn is_conflicted(&self) -> bool {
        self.0.with_data(|d| d.types.len() > 1)
    }

    fn is_locked(&self) -> bool {
        debug_assert!(self.0.with_data(|d| d.locked != d.types.is_empty()));

        self.0.with_data(|d| d.locked)
    }

    fn clone_types(&self) -> HashMap<TypeKey, PotentialType> {
        self.0.with_data(|d| d.types.clone())
    }

    fn set_flag_missing_info(&self) {
        self.0.with_data(|d| d.missing_info = true);
    }

    fn merge(mut tyvar1: TypeVar, mut tyvar2: TypeVar) {
        tyvar1.0.union_with(&mut tyvar2.0, TypeVarData::merge_data);
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
        node: AstNode,
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
            PotentialType::Poly(_, ref decl) => {
                if !polyvar_scope.lookup_poly(decl) {
                    let polyty = &decl.0;
                    let prov = Prov::InstantiatePoly(node.clone(), polyty.clone());
                    let ret = TypeVar::fresh(ctx, prov.clone());
                    let mut extension: Vec<(Rc<InterfaceDecl>, AstNode)> = Vec::new();
                    for i in &polyty.iface_names {
                        if let Some(Declaration::InterfaceDef(iface)) =
                            ctx.resolution_map.get(&i.id)
                        {
                            extension.push((iface.clone(), node.clone()));
                        }
                    }
                    ctx.unifvars_constrained_to_interfaces
                        .entry(prov)
                        .or_default()
                        .extend(extension);
                    return ret; // instantiation occurs here
                } else {
                    ty // noop
                }
            }
            PotentialType::Nominal(provs, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, node.clone()))
                    .collect();
                PotentialType::Nominal(provs, ident, params)
            }
            PotentialType::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, node.clone()))
                    .collect();
                let out = out.instantiate(polyvar_scope.clone(), ctx, node.clone());
                PotentialType::Function(provs, args, out)
            }
            PotentialType::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, node.clone()))
                    .collect();
                PotentialType::Tuple(provs, elems)
            }
        };
        let mut types = HashMap::default();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData {
            types,
            locked: data.locked,
            missing_info: data.missing_info,
        };
        let tvar = TypeVar(UnionFindNode::new(data_instantiated));
        ctx.unifvars.insert(Prov::Node(node), tvar.clone());
        tvar
    }

    pub(crate) fn get_first_polymorphic_type(self) -> Option<PolyDeclaration> {
        let data = self.0.clone_data();
        if data.types.len() == 1 {
            let ty = data.types.into_values().next().unwrap();

            match ty {
                PotentialType::Unit(_)
                | PotentialType::Int(_)
                | PotentialType::Float(_)
                | PotentialType::Bool(_)
                | PotentialType::String(_) => None,
                PotentialType::Poly(_, decl) => Some(decl.clone()),
                PotentialType::Nominal(_, _, params) => {
                    for param in &params {
                        if let Some(decl) = param.clone().get_first_polymorphic_type() {
                            return Some(decl);
                        }
                    }
                    None
                }
                PotentialType::Function(_, args, out) => {
                    for arg in &args {
                        if let Some(decl) = arg.clone().get_first_polymorphic_type() {
                            return Some(decl);
                        }
                    }
                    out.get_first_polymorphic_type()
                }
                PotentialType::Tuple(_, elems) => {
                    for elem in &elems {
                        if let Some(decl) = elem.clone().get_first_polymorphic_type() {
                            return Some(decl);
                        }
                    }
                    None
                }
            }
        } else {
            None
        }
    }

    pub(crate) fn subst(self, substitution: &Substitution) -> TypeVar {
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
                PotentialType::Poly(_, ref decl) => {
                    if let Some(new_ty) = substitution.get(decl) {
                        return new_ty.clone(); // substitution occurs here
                    } else {
                        ty // noop
                    }
                }
                PotentialType::Nominal(provs, ident, params) => {
                    let params = params
                        .into_iter()
                        .map(|ty| ty.subst(substitution))
                        .collect();
                    PotentialType::Nominal(provs, ident, params)
                }
                PotentialType::Function(provs, args, out) => {
                    let args = args.into_iter().map(|ty| ty.subst(substitution)).collect();
                    let out = out.subst(substitution);
                    PotentialType::Function(provs, args, out)
                }
                PotentialType::Tuple(provs, elems) => {
                    let elems = elems.into_iter().map(|ty| ty.subst(substitution)).collect();
                    PotentialType::Tuple(provs, elems)
                }
            };
            let mut types = HashMap::default();
            types.insert(ty.key(), ty);
            let new_data = TypeVarData {
                types,
                locked: data.locked,
                missing_info: data.missing_info,
            };
            TypeVar(UnionFindNode::new(new_data))
        } else {
            self // noop
        }
    }

    pub(crate) fn from_node(ctx: &mut StaticsContext, node: AstNode) -> TypeVar {
        let prov = Prov::Node(node);
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

    pub(crate) fn empty() -> TypeVar {
        TypeVar(UnionFindNode::new(TypeVarData::new()))
    }

    fn singleton_solved(potential_type: PotentialType) -> TypeVar {
        TypeVar(UnionFindNode::new(TypeVarData::singleton_solved(
            potential_type,
        )))
    }

    pub(crate) fn make_unit(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_unit(reason))
    }

    pub(crate) fn make_int(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_int(reason))
    }

    pub(crate) fn make_float(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_float(reason))
    }

    pub(crate) fn make_bool(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_bool(reason))
    }

    pub(crate) fn make_string(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_string(reason))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_func(args, out, reason))
    }

    pub(crate) fn make_tuple(elems: Vec<TypeVar>, reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_tuple(elems, reason))
    }

    pub(crate) fn make_poly(reason: Reason, decl: PolyDeclaration) -> TypeVar {
        Self::singleton_solved(PotentialType::make_poly(reason, decl))
    }

    pub(crate) fn make_nominal(reason: Reason, nominal: Nominal, params: Vec<TypeVar>) -> TypeVar {
        Self::singleton_solved(PotentialType::make_nominal(reason, nominal, params))
    }

    // Make nominal type with skolems substituted for type arguments. Return type and the substitution (mapping from type argument to skolem that replaced it)
    pub(crate) fn make_nominal_with_substitution(
        reason: Reason,
        nominal: Nominal,
        ctx: &mut StaticsContext,
        node: AstNode,
    ) -> (TypeVar, Substitution) {
        let mut substitution: Substitution = HashMap::default();
        let mut params: Vec<TypeVar> = vec![];

        let mut helper = |ty_args: &Vec<Rc<Polytype>>| {
            for i in 0..ty_args.len() {
                params.push(TypeVar::fresh(
                    ctx,
                    Prov::InstantiateUdtParam(node.clone(), i as u8),
                ));
                let polyty = &ty_args[i];
                if let Some(Declaration::Polytype(decl)) = ctx.resolution_map.get(&polyty.name.id) {
                    substitution.insert(PolyDeclaration(decl.clone()), params[i].clone());
                };
            }
        };

        match &nominal {
            Nominal::Struct(struct_def) => helper(&struct_def.ty_args),
            Nominal::Enum(enum_def) => helper(&enum_def.ty_args),
            Nominal::Array => {
                params.push(TypeVar::fresh(
                    ctx,
                    Prov::InstantiateUdtParam(node.clone(), 0),
                ));
                // substitution is left empty for array because it's not used.
            }
        }

        (TypeVar::make_nominal(reason, nominal, params), substitution)
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

fn tyvar_of_declaration(
    ctx: &mut StaticsContext,
    decl: &Declaration,
    node: AstNode,
) -> Option<TypeVar> {
    match decl {
        Declaration::FreeFunction(f, _) => Some(TypeVar::from_node(ctx, f.name.node())),
        Declaration::HostFunction(f, _) => Some(TypeVar::from_node(ctx, f.name.node())),
        Declaration::_ForeignFunction { decl, .. } => {
            Some(TypeVar::from_node(ctx, decl.name.node()))
        }
        Declaration::InterfaceDef(..) => None,
        Declaration::InterfaceMethod {
            iface_def,
            method,
            fully_qualified_name: _,
        } => Some(TypeVar::from_node(
            ctx,
            iface_def.methods[*method as usize].node(),
        )),
        Declaration::Enum(enum_def) => {
            let nparams = enum_def.ty_args.len();
            let mut params = vec![];
            for i in 0..nparams {
                params.push(TypeVar::fresh(
                    ctx,
                    Prov::InstantiateUdtParam(node.clone(), i as u8),
                ));
            }
            Some(TypeVar::make_nominal(
                Reason::Node(node), // TODO: change to Reason::Declaration
                Nominal::Enum(enum_def.clone()),
                params,
            ))
        }
        Declaration::EnumVariant { enum_def, variant } => {
            let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                Reason::Node(node.clone()),
                Nominal::Enum(enum_def.clone()),
                ctx,
                node.clone(),
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
                                e.clone().subst(&substitution)
                            })
                            .collect();
                        Some(TypeVar::make_func(args, def_type, Reason::Node(node)))
                    }
                    _ => {
                        let ty = ast_type_to_typevar(ctx, ty.clone());
                        Some(TypeVar::make_func(
                            vec![ty.clone().subst(&substitution)],
                            def_type,
                            Reason::Node(node.clone()),
                        ))
                    }
                },
            }
        }
        Declaration::Struct(struct_def) => {
            let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                Reason::Node(node.clone()),
                Nominal::Struct(struct_def.clone()),
                ctx,
                node.clone(),
            );

            let fields = struct_def
                .fields
                .iter()
                .map(|f| {
                    let ty = ast_type_to_typevar(ctx, f.ty.clone());
                    ty.clone().subst(&substitution)
                })
                .collect();
            Some(TypeVar::make_func(fields, def_type, Reason::Node(node)))
        }
        Declaration::Array => {
            let params = vec![TypeVar::fresh(
                ctx,
                Prov::InstantiateUdtParam(node.clone(), 0),
            )];
            let def_type =
                TypeVar::make_nominal(Reason::Node(node.clone()), Nominal::Array, params);
            Some(TypeVar::make_func(vec![], def_type, Reason::Node(node)))
        }
        Declaration::Polytype(polytype) => Some(TypeVar::make_poly(
            Reason::Annotation(node),
            PolyDeclaration(polytype.clone()),
        )),
        Declaration::Builtin(builtin) => {
            let ty_signature = builtin.type_signature();
            Some(ty_signature)
        }
        Declaration::Var(node) => Some(TypeVar::from_node(ctx, node.clone())),
    }
}

pub(crate) fn ast_type_to_solved_type(
    ctx: &StaticsContext,
    ast_type: Rc<AstType>,
) -> Option<SolvedType> {
    match &*ast_type.kind {
        TypeKind::Poly(polyty) => Some(SolvedType::Poly(polyty.clone())),
        TypeKind::Named(_) => {
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
                Declaration::_ForeignFunction { .. }
                | Declaration::FreeFunction(_, _)
                | Declaration::HostFunction(..)
                | Declaration::InterfaceDef(_)
                | Declaration::InterfaceMethod { .. }
                | Declaration::EnumVariant { .. }
                | Declaration::Polytype(_)
                | Declaration::Builtin(_)
                | Declaration::Var(_) => None,
            }
        }
        TypeKind::NamedWithParams(identifier, args) => {
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
                Declaration::_ForeignFunction { .. }
                | Declaration::HostFunction(..)
                | Declaration::FreeFunction(_, _)
                | Declaration::InterfaceDef(_)
                | Declaration::InterfaceMethod { .. }
                | Declaration::EnumVariant { .. }
                | Declaration::Polytype(_)
                | Declaration::Builtin(_)
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

pub(crate) fn ast_type_to_typevar(ctx: &StaticsContext, ast_type: Rc<AstType>) -> TypeVar {
    match &*ast_type.kind {
        TypeKind::Poly(polyty) => {
            if let Some(Declaration::Polytype(polyty)) = ctx.resolution_map.get(&polyty.name.id) {
                TypeVar::make_poly(
                    Reason::Annotation(ast_type.node()),
                    PolyDeclaration(polyty.clone()),
                )
            } else {
                TypeVar::empty()
            }
        }
        TypeKind::Named(_) => {
            let lookup = ctx.resolution_map.get(&ast_type.id);
            match lookup {
                Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.node()),
                    Nominal::Enum(enum_def.clone()),
                    vec![], // TODO: why is params empty?
                ),
                Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.node()),
                    Nominal::Struct(struct_def.clone()),
                    vec![], // TODO: why is params empty?
                ),
                Some(Declaration::Array) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.node()),
                    Nominal::Array,
                    vec![], // TODO: why is params empty?
                ),
                _ => {
                    // since resolution failed, unconstrained type
                    TypeVar::empty()
                }
            }
        }
        TypeKind::NamedWithParams(ident, params) => {
            let lookup = ctx.resolution_map.get(&ident.id);
            match lookup {
                Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.node()),
                    Nominal::Enum(enum_def.clone()),
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.node()),
                    Nominal::Struct(struct_def.clone()),
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                Some(Declaration::Array) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.node()),
                    Nominal::Array,
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                _ => {
                    // since resolution failed, unconstrained type
                    TypeVar::empty()
                }
            }
        }
        TypeKind::Unit => TypeVar::make_unit(Reason::Annotation(ast_type.node())),
        TypeKind::Int => TypeVar::make_int(Reason::Annotation(ast_type.node())),
        TypeKind::Float => TypeVar::make_float(Reason::Annotation(ast_type.node())),
        TypeKind::Bool => TypeVar::make_bool(Reason::Annotation(ast_type.node())),
        TypeKind::Str => TypeVar::make_string(Reason::Annotation(ast_type.node())),
        TypeKind::Function(lhs, rhs) => TypeVar::make_func(
            lhs.iter()
                .map(|t| ast_type_to_typevar(ctx, t.clone()))
                .collect(),
            ast_type_to_typevar(ctx, rhs.clone()),
            Reason::Annotation(ast_type.node()),
        ),
        TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_typevar(ctx, t.clone()));
            }
            TypeVar::make_tuple(statics_types, Reason::Annotation(ast_type.node()))
        }
    }
}

pub(crate) type Reasons = RefCell<BTreeSet<Reason>>;

fn reasons_singleton(reason: Reason) -> Reasons {
    let mut set = BTreeSet::new();
    set.insert(reason);
    RefCell::new(set)
}

// TODO: is Mode really necessary?
#[derive(Debug, Clone)]
pub(crate) enum Mode {
    Syn,
    Ana {
        expected: TypeVar,
    },
    AnaWithReason {
        expected: TypeVar,
        constraint_reason: ConstraintReason,
    },
}

// TODO: There's a lot of calls to constrain() that should use a different function like init_typevar()
// which will panic if the typevar is not unconstrained. init_typevar() would not take a ConstraintReason
// because we're not constraining one type to another.

// TODO: Go through each call to constrain() one-by-one to see if it should be replaced with constrain_because
// TODO: After that, perhaps ConstraintReason::None should be removed altogether.
pub(crate) fn constrain(ctx: &mut StaticsContext, tyvar1: TypeVar, tyvar2: TypeVar) {
    constrain_because(ctx, tyvar1, tyvar2, ConstraintReason::None)
}

pub(crate) fn constrain_because(
    ctx: &mut StaticsContext,
    tyvar1: TypeVar,
    tyvar2: TypeVar,
    constraint_reason: ConstraintReason,
) {
    match (tyvar1.is_locked(), tyvar2.is_locked()) {
        // Since both TypeVars are already locked, an error is logged if their data do not match
        (true, true) => {
            constrain_locked_typevars(ctx, tyvar1, tyvar2, constraint_reason);
        }
        // Since exactly one of the TypeVars is unsolved, its data will be updated with information from the solved TypeVar
        (false, true) => {
            let potential_ty = tyvar2.0.clone_data().types.into_iter().next().unwrap().1;
            tyvar1.0.with_data(|d: &mut TypeVarData| {
                if d.types.is_empty() {
                    assert!(!d.locked);
                    d.locked = true
                }
                d.extend(potential_ty)
            });
        }
        (true, false) => {
            let potential_ty = tyvar1.0.clone_data().types.into_iter().next().unwrap().1;
            tyvar2.0.with_data(|d| {
                if d.types.is_empty() {
                    assert!(!d.locked);
                    d.locked = true
                }
                d.extend(potential_ty)
            });
        }
        // Since both TypeVars are unsolved, they are unioned and their data is merged
        (false, false) => {
            TypeVar::merge(tyvar1, tyvar2);
        }
    }
}

pub(crate) fn constrain_to_iface(
    ctx: &mut StaticsContext,
    tyvar: TypeVar,
    node: AstNode,
    iface: &Rc<InterfaceDecl>,
) {
    if let Some(ty) = tyvar.solution() {
        if !ty_implements_iface(ctx, ty.clone(), iface) {
            ctx.errors.push(Error::InterfaceNotImplemented {
                ty: ty.clone(),
                iface: iface.clone(),
                node,
            });
        }
    } else {
        let ifaces = ctx
            .unifvars_constrained_to_interfaces
            .entry(Prov::Node(node.clone()))
            .or_default();
        ifaces.push((iface.clone(), node));
    }
}

fn constrain_locked_typevars(
    ctx: &mut StaticsContext,
    tyvar1: TypeVar,
    tyvar2: TypeVar,
    constraint_reason: ConstraintReason,
) {
    let (key1, potential_ty1) = tyvar1.0.clone_data().types.into_iter().next().unwrap();
    let (key2, potential_ty2) = tyvar2.0.clone_data().types.into_iter().next().unwrap();
    if key1 != key2 {
        ctx.errors.push(Error::TypeConflict {
            ty1: potential_ty1,
            ty2: potential_ty2,
            constraint_reason,
        })
    } else {
        match (potential_ty1, potential_ty2) {
            (PotentialType::Function(_, args1, out1), PotentialType::Function(_, args2, out2)) => {
                for (arg1, arg2) in args1.iter().zip(args2.iter()) {
                    constrain_because(ctx, arg1.clone(), arg2.clone(), constraint_reason.clone());
                }
                constrain_because(ctx, out1, out2, constraint_reason);
            }
            (PotentialType::Tuple(_, elems1), PotentialType::Tuple(_, elems2)) => {
                for (elem1, elem2) in elems1.iter().zip(elems2.iter()) {
                    constrain_because(ctx, elem1.clone(), elem2.clone(), constraint_reason.clone());
                }
            }
            (PotentialType::Nominal(_, _, tyvars1), PotentialType::Nominal(_, _, tyvars2)) => {
                for (tyvar1, tyvar2) in tyvars1.iter().zip(tyvars2.iter()) {
                    constrain_because(
                        ctx,
                        tyvar1.clone(),
                        tyvar2.clone(),
                        constraint_reason.clone(),
                    );
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone)]
pub(crate) struct PolyvarScope {
    polyvars_in_scope: Environment<PolyDeclaration, ()>,
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
            PotentialType::Poly(_, decl) => {
                self.polyvars_in_scope.extend(decl.clone(), ());
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

    fn lookup_poly(&self, decl: &PolyDeclaration) -> bool {
        self.polyvars_in_scope.lookup(decl).is_some()
    }

    fn new_scope(&self) -> Self {
        Self {
            polyvars_in_scope: self.polyvars_in_scope.new_scope(),
        }
    }
}

pub(crate) fn check_unifvars(ctx: &mut StaticsContext) {
    if !ctx.errors.is_empty() {
        // Don't display errors for global inference unless earlier
        // errors are fixed to avoid redundant feedback
        return;
    }
    // get list of type conflicts
    let mut type_conflicts = Vec::new();
    for (prov, tyvar) in ctx.unifvars.iter() {
        if tyvar.is_conflicted() {
            let type_suggestions = tyvar.clone_types();
            if !type_conflicts.contains(&type_suggestions) {
                type_conflicts.push(type_suggestions.clone());

                ctx.errors.push(Error::ConflictingUnifvar {
                    types: type_suggestions,
                });
            }
        } else if tyvar.is_underdetermined() {
            if let Prov::Node(id) = prov {
                ctx.errors
                    .push(Error::UnconstrainedUnifvar { node: id.clone() });
            }
        }
    }
    for (prov, ifaces) in &ctx.unifvars_constrained_to_interfaces {
        let ty = ctx.unifvars.get(prov).unwrap().clone();
        if let Some(ty) = ty.solution() {
            for (iface, node) in ifaces.iter().cloned() {
                if !ty_implements_iface(ctx, ty.clone(), &iface) {
                    ctx.errors.push(Error::InterfaceNotImplemented {
                        ty: ty.clone(),
                        iface,
                        node,
                    });
                }
            }
        }
    }
}

pub(crate) fn generate_constraints_file_decls(file: Rc<FileAst>, ctx: &mut StaticsContext) {
    for items in file.items.iter() {
        generate_constraints_item_decls(items.clone(), ctx);
    }
}

fn generate_constraints_item_decls(item: Rc<Item>, ctx: &mut StaticsContext) {
    match &*item.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(_) => {}
        ItemKind::InterfaceImpl(iface_impl) => {
            let lookup = ctx.resolution_map.get(&iface_impl.iface.id).cloned();
            if let Some(Declaration::InterfaceDef(iface_decl)) = &lookup {
                for method in &iface_decl.methods {
                    let node_ty = TypeVar::from_node(ctx, method.node());
                    if node_ty.is_locked() {
                        // Interface declaration method types have already been computed.
                        break;
                    }
                    let ty_annot = ast_type_to_typevar(ctx, method.ty.clone());
                    // TODO: Instead of creating an empty TypeVar (node_ty) and then immediately constraining it to a
                    // typevar created from a type annotation (ast_type_to_typevar(ty_annot)), do both in a single atomic step
                    constrain(ctx, node_ty.clone(), ty_annot.clone());
                }

                let impl_list = ctx.interface_impls.entry(iface_decl.clone()).or_default();

                impl_list.push(iface_impl.clone());
            }

            // todo last here
        }
        ItemKind::TypeDef(typdefkind) => match &**typdefkind {
            // TypeDefKind::Alias(ident, ty) => {
            //     let left = TypeVar::fresh(ctx, Prov::Alias(ident.clone()));
            //     let right = ast_type_to_statics_type(ctx, ty.clone());
            //     constrain(ctx,left, right);
            // }
            TypeDefKind::Enum(..) | TypeDefKind::Struct(..) => {}
        },
        ItemKind::FuncDef(f) => {
            generate_constraints_func_decl(
                ctx,
                f.name.node(),
                PolyvarScope::empty(),
                &f.args,
                &f.ret_type,
            );
        }
        ItemKind::HostFuncDecl(f) | ItemKind::ForeignFuncDecl(f) => {
            generate_constraints_func_decl_annotated(
                ctx,
                f.name.node(),
                PolyvarScope::empty(),
                &f.args,
                &Some(f.ret_type.clone()),
            );
        }
    }
}

pub(crate) fn generate_constraints_file_stmts(file: Rc<FileAst>, ctx: &mut StaticsContext) {
    for items in file.items.iter() {
        generate_constraints_item_stmts(Mode::Syn, items.clone(), ctx);
    }
}

fn generate_constraints_item_stmts(mode: Mode, stmt: Rc<Item>, ctx: &mut StaticsContext) {
    match &*stmt.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(stmt) => {
            generate_constraints_stmt(PolyvarScope::empty(), mode, stmt.clone(), ctx)
        }
        ItemKind::InterfaceImpl(iface_impl) => {
            let impl_ty = ast_type_to_typevar(ctx, iface_impl.typ.clone());

            if impl_ty.is_instantiated_nominal() {
                ctx.errors.push(Error::InterfaceImplTypeNotGeneric {
                    node: iface_impl.typ.node(),
                })
            }

            let lookup = ctx.resolution_map.get(&iface_impl.iface.id).cloned();
            if let Some(Declaration::InterfaceDef(iface_decl)) = &lookup {
                for f in &iface_impl.methods {
                    let method_name = f.name.v.clone();
                    if let Some(interface_method) =
                        iface_decl.methods.iter().find(|m| m.name.v == method_name)
                    {
                        let interface_method_ty =
                            ast_type_to_typevar(ctx, interface_method.ty.clone());
                        let actual = TypeVar::from_node(ctx, interface_method.node());
                        constrain(ctx, interface_method_ty.clone(), actual);

                        let mut substitution: Substitution = HashMap::default();
                        if let Some(poly_decl) =
                            interface_method_ty.clone().get_first_polymorphic_type()
                        {
                            substitution.insert(poly_decl, impl_ty.clone());
                        }

                        let expected = interface_method_ty.clone().subst(&substitution);

                        let actual = TypeVar::from_node(ctx, f.name.node());
                        constrain(ctx, expected, actual);

                        generate_constraints_fn_def(ctx, PolyvarScope::empty(), f, f.name.node());
                    }
                }
            }
        }
        ItemKind::TypeDef(_) => {}
        ItemKind::FuncDef(f) => {
            generate_constraints_fn_def(ctx, PolyvarScope::empty(), f, f.name.node());
        }
        ItemKind::HostFuncDecl(_) | ItemKind::ForeignFuncDecl(_) => {}
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
            let ty_pat = TypeVar::from_node(ctx, pat.node());

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_typevar(ctx, ty_ann.clone());

                generate_constraints_pat(
                    polyvar_scope.clone(),
                    Mode::AnaWithReason {
                        expected: ty_ann,
                        constraint_reason: ConstraintReason::LetStmtAnnotation,
                    },
                    pat.clone(),
                    ctx,
                )
            } else {
                generate_constraints_pat(polyvar_scope.clone(), Mode::Syn, pat.clone(), ctx)
            };

            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: ty_pat,
                    constraint_reason: ConstraintReason::LetSetLhsRhs,
                },
                expr.clone(),
                ctx,
            );
        }
        StmtKind::Set(lhs, rhs) => {
            let ty_lhs = TypeVar::from_node(ctx, lhs.node());
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, lhs.clone(), ctx);
            generate_constraints_expr(
                polyvar_scope,
                Mode::AnaWithReason {
                    expected: ty_lhs,
                    constraint_reason: ConstraintReason::LetSetLhsRhs,
                },
                rhs.clone(),
                ctx,
            );
        }
        StmtKind::Break | StmtKind::Continue => {
            let enclosing_loop = ctx.loop_stack.last();
            match enclosing_loop {
                None | Some(None) => {
                    ctx.errors.push(Error::NotInLoop { node: stmt.node() });
                }
                Some(Some(_node)) => {}
            }
        }
        StmtKind::Return(expr) => {
            let expr_ty = TypeVar::from_node(ctx, expr.node());
            generate_constraints_expr(polyvar_scope, Mode::Syn, expr.clone(), ctx);
            let enclosing_func_ret = ctx.func_ret_stack.last();
            match enclosing_func_ret {
                Some(prov) => {
                    let ret_ty = TypeVar::fresh(ctx, prov.clone());
                    constrain_because(ctx, expr_ty, ret_ty, ConstraintReason::ReturnValue);
                }
                None => {
                    todo!()
                }
            }
        }
    }
}

fn generate_constraints_expr(
    polyvar_scope: PolyvarScope,
    mode: Mode,
    expr: Rc<Expr>,
    ctx: &mut StaticsContext,
) {
    let node_ty = TypeVar::from_node(ctx, expr.node());
    match &*expr.kind {
        ExprKind::Unit => {
            constrain(
                ctx,
                node_ty,
                TypeVar::make_unit(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Int(_) => {
            constrain(
                ctx,
                node_ty,
                TypeVar::make_int(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Float(_) => {
            constrain(
                ctx,
                node_ty,
                TypeVar::make_float(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Bool(_) => {
            constrain(
                ctx,
                node_ty,
                TypeVar::make_bool(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Str(s) => {
            constrain(
                ctx,
                node_ty,
                TypeVar::make_string(Reason::Literal(expr.node())),
            );
            ctx.string_constants.insert(s.clone());
        }
        ExprKind::List(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(expr.node()));

            let list_decl = ctx.root_namespace.get_declaration("prelude.list");

            if let Some(Declaration::Enum(enum_def)) = list_decl {
                constrain(
                    ctx,
                    node_ty,
                    TypeVar::make_nominal(
                        Reason::Node(expr.node()),
                        Nominal::Enum(enum_def.clone()),
                        vec![elem_ty.clone()],
                    ),
                );
            } else {
                dbg!(list_decl);
                todo!();
                // TODO: log error? Or panic? Could this happen due to user error, or is it always due to some internal compiler error
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
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(expr.node()));
            constrain(
                ctx,
                node_ty,
                TypeVar::make_nominal(
                    Reason::Node(expr.node()),
                    Nominal::Array,
                    vec![elem_ty.clone()],
                ),
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
        ExprKind::Variable(_) => {
            let lookup = ctx.resolution_map.get(&expr.id).cloned();
            if let Some(res) = lookup {
                if let Some(typ) = tyvar_of_declaration(ctx, &res, expr.node()) {
                    // TODO: tyvar_of_declaration should probably do the instantiation for you, instead of having to remember
                    let typ = typ.instantiate(polyvar_scope, ctx, expr.node());
                    constrain(ctx, typ, node_ty.clone());
                }
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let ty_left = TypeVar::from_node(ctx, left.node());
            let ty_right = TypeVar::from_node(ctx, right.node());
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, left.clone(), ctx);
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, right.clone(), ctx);
            let ty_out = node_ty;

            let num_iface_decl = ctx.root_namespace.get_declaration("prelude.Num").unwrap();
            let Declaration::InterfaceDef(num_iface) = num_iface_decl else { unreachable!() };

            let equal_iface_decl = ctx.root_namespace.get_declaration("prelude.Equal").unwrap();
            let Declaration::InterfaceDef(equal_iface) = equal_iface_decl else { unreachable!() };

            let tostring_iface_decl = ctx
                .root_namespace
                .get_declaration("prelude.ToString")
                .unwrap();
            let Declaration::InterfaceDef(tostring_iface) = tostring_iface_decl else {
                unreachable!()
            };

            let reason_left = Reason::BinopLeft(expr.node());
            let reason_right = Reason::BinopRight(expr.node());
            let reason_out = Reason::BinopOut(expr.node());
            match op {
                BinaryOperator::And | BinaryOperator::Or => {
                    constrain_because(
                        ctx,
                        ty_left,
                        TypeVar::make_bool(reason_left),
                        ConstraintReason::BinaryOperandBool(expr.node()),
                    );
                    constrain_because(
                        ctx,
                        ty_right,
                        TypeVar::make_bool(reason_right),
                        ConstraintReason::BinaryOperandBool(expr.node()),
                    );
                    constrain(ctx, ty_out, TypeVar::make_bool(reason_out));
                }
                BinaryOperator::Add
                | BinaryOperator::Subtract
                | BinaryOperator::Multiply
                | BinaryOperator::Divide
                | BinaryOperator::Pow => {
                    constrain_because(
                        ctx,
                        ty_left.clone(),
                        ty_right.clone(),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                    constrain_to_iface(ctx, ty_left.clone(), left.node(), &num_iface);
                    constrain_to_iface(ctx, ty_right, right.node(), &num_iface);
                    constrain(ctx, ty_left, ty_out);
                }
                BinaryOperator::Mod => {
                    constrain_because(
                        ctx,
                        ty_left,
                        TypeVar::make_int(reason_left),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                    constrain_because(
                        ctx,
                        ty_right,
                        TypeVar::make_int(reason_right),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                    constrain(ctx, ty_out, TypeVar::make_int(reason_out));
                }
                BinaryOperator::LessThan
                | BinaryOperator::GreaterThan
                | BinaryOperator::LessThanOrEqual
                | BinaryOperator::GreaterThanOrEqual => {
                    constrain_because(
                        ctx,
                        ty_left.clone(),
                        ty_right.clone(),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                    constrain_to_iface(ctx, ty_left, left.node(), &num_iface);
                    constrain_to_iface(ctx, ty_right, right.node(), &num_iface);
                    constrain(ctx, ty_out, TypeVar::make_bool(reason_out));
                }
                BinaryOperator::Format => {
                    constrain_to_iface(ctx, ty_left.clone(), left.node(), &tostring_iface);
                    constrain_to_iface(ctx, ty_right.clone(), right.node(), &tostring_iface);
                    constrain_because(
                        ctx,
                        ty_out,
                        TypeVar::make_string(reason_out),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                }
                BinaryOperator::Equal => {
                    constrain_because(
                        ctx,
                        ty_left.clone(),
                        ty_right.clone(),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                    constrain_to_iface(ctx, ty_left.clone(), left.node(), &equal_iface);
                    constrain_to_iface(ctx, ty_right.clone(), right.node(), &equal_iface);
                    constrain(ctx, ty_out, TypeVar::make_bool(reason_out));
                }
            }
        }
        ExprKind::Block(statements) => {
            if statements.is_empty() {
                constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.node())));
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
            } else if let StmtKind::Return(_) = &*statements.last().unwrap().kind {
                generate_constraints_stmt(
                    polyvar_scope.clone(),
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                    ctx,
                );
            } else {
                generate_constraints_stmt(
                    polyvar_scope,
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                    ctx,
                );
                constrain(ctx, node_ty, TypeVar::make_unit(Reason::Node(expr.node())))
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.node())),
                    constraint_reason: ConstraintReason::Condition,
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
                        polyvar_scope.clone(),
                        Mode::AnaWithReason {
                            expected: node_ty.clone(),
                            constraint_reason: ConstraintReason::IfElseBodies,
                        },
                        expr2.clone(),
                        ctx,
                    );
                }
                // just if
                None => {
                    generate_constraints_expr(
                        polyvar_scope,
                        Mode::Ana {
                            expected: TypeVar::make_unit(Reason::IfWithoutElse(expr.node())),
                        },
                        expr1.clone(),
                        ctx,
                    );
                    constrain(
                        ctx,
                        node_ty,
                        TypeVar::make_unit(Reason::IfWithoutElse(expr.node())),
                    )
                }
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.node())),
                    constraint_reason: ConstraintReason::Condition,
                },
                cond.clone(),
                ctx,
            );
            ctx.loop_stack.push(Some(expr.id));
            generate_constraints_expr(polyvar_scope, Mode::Syn, expr.clone(), ctx);
            ctx.loop_stack.pop();
            constrain(
                ctx,
                node_ty,
                TypeVar::make_unit(Reason::WhileLoopBody(expr.node())),
            )
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = TypeVar::from_node(ctx, scrut.node());
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
                    Mode::AnaWithReason {
                        expected: ty_scrutiny.clone(),
                        constraint_reason: ConstraintReason::MatchScrutinyAndPattern,
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
        ExprKind::AnonymousFunction(args, out_annot, body) => {
            let func_node = expr.node();
            let ty_func = generate_constraints_func_helper(
                ctx,
                func_node,
                polyvar_scope,
                args,
                out_annot,
                body,
            );

            constrain(ctx, node_ty, ty_func);
        }
        ExprKind::FuncAp(func, args) => {
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, func.clone(), ctx);
            let ty_func = TypeVar::from_node(ctx, func.node());

            // arguments
            let tys_args: Vec<TypeVar> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = TypeVar::fresh(ctx, Prov::FuncArg(func.node(), n as u8));
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
            let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(func.node()));
            constrain(ctx, ty_body.clone(), node_ty);

            // function type
            let ty_args_and_body = TypeVar::make_func(tys_args, ty_body, Reason::Node(expr.node()));

            constrain_because(
                ctx,
                ty_args_and_body.clone(),
                ty_func.clone(),
                ConstraintReason::FuncCall(expr.node()),
            );
        }
        ExprKind::Tuple(exprs) => {
            let tys = exprs
                .iter()
                .map(|expr| TypeVar::fresh(ctx, Prov::Node(expr.node())))
                .collect();
            constrain(
                ctx,
                node_ty,
                TypeVar::make_tuple(tys, Reason::Node(expr.node())),
            );
            for expr in exprs {
                generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, expr.clone(), ctx);
            }
        }
        /*
         * This could be one of multiple situations
         * - struct member access (runtime)
         * - qualified enum variant
         * - ...
         */
        ExprKind::MemberAccess(expr, member_ident) => {
            if let Some(ref decl @ Declaration::EnumVariant { .. }) =
                ctx.resolution_map.get(&member_ident.id).cloned()
            {
                if let Some(ty_of_declaration) = tyvar_of_declaration(ctx, decl, expr.node()) {
                    let typ = ty_of_declaration.instantiate(polyvar_scope, ctx, expr.node());
                    constrain(ctx, node_ty, typ);
                }
            } else {
                generate_constraints_expr(polyvar_scope, Mode::Syn, expr.clone(), ctx);
                let ty_expr = TypeVar::from_node(ctx, expr.node());
                if ty_expr.underdetermined() {
                    ctx.errors
                        .push(Error::MemberAccessNeedsAnnotation { node: expr.node() });
                    return;
                }
                let Some(inner) = ty_expr.single() else {
                    return;
                };
                if let PotentialType::Nominal(_, Nominal::Struct(struct_def), _) = inner {
                    let mut resolved = false;
                    for field in &struct_def.fields {
                        if field.name.v == *member_ident.v {
                            let ty_field = ast_type_to_typevar(ctx, field.ty.clone());
                            constrain(ctx, node_ty.clone(), ty_field);
                            resolved = true;
                        }
                    }
                    if !resolved {
                        ctx.errors.push(Error::UnresolvedIdentifier {
                            node: member_ident.node(),
                        })
                    }
                }
            }
        }
        ExprKind::MemberAccessInferred(ident) => {
            let expected_ty = match mode.clone() {
                Mode::Syn => None,
                Mode::AnaWithReason {
                    expected,
                    constraint_reason: _,
                }
                | Mode::Ana { expected } => Some(expected),
            };

            let mut can_infer = false;
            if let Some(expected_ty) = expected_ty {
                if let Some(SolvedType::Nominal(Nominal::Enum(enum_def), _)) =
                    expected_ty.solution()
                {
                    can_infer = true;

                    let mut idx: u16 = 0;
                    for (i, variant) in enum_def.variants.iter().enumerate() {
                        if variant.ctor.v == ident.v {
                            idx = i as u16;
                        }
                    }

                    ctx.resolution_map.insert(
                        ident.id,
                        Declaration::EnumVariant {
                            enum_def: enum_def.clone(),
                            variant: idx,
                        },
                    );

                    let enum_ty =
                        tyvar_of_declaration(ctx, &Declaration::Enum(enum_def), expr.node())
                            .unwrap();
                    let enum_ty = enum_ty.instantiate(polyvar_scope, ctx, expr.node());

                    constrain(ctx, node_ty.clone(), enum_ty);
                }
            }

            if !can_infer {
                ctx.errors
                    .push(Error::UnqualifiedEnumNeedsAnnotation { node: expr.node() });

                node_ty.set_flag_missing_info();
            }
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, accessed.clone(), ctx);

            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(accessed.node()));
            let accessed_ty = TypeVar::from_node(ctx, accessed.node());
            constrain(
                ctx,
                accessed_ty,
                TypeVar::make_nominal(
                    Reason::Node(accessed.node()),
                    Nominal::Array,
                    vec![elem_ty.clone()],
                ),
            );
            generate_constraints_expr(
                polyvar_scope,
                Mode::AnaWithReason {
                    expected: TypeVar::make_int(Reason::IndexAccess),
                    constraint_reason: ConstraintReason::IndexAccess,
                },
                index.clone(),
                ctx,
            );

            constrain(ctx, node_ty, elem_ty);
        }
    }
    let node_ty = TypeVar::from_node(ctx, expr.node());
    match mode {
        Mode::Syn => (),
        Mode::AnaWithReason {
            expected,
            constraint_reason,
        } => constrain_because(ctx, node_ty.clone(), expected, constraint_reason),
        Mode::Ana { expected } => constrain(ctx, node_ty.clone(), expected),
    };
}

fn generate_constraints_func_helper(
    ctx: &mut StaticsContext,
    node: AstNode,
    polyvar_scope: PolyvarScope,
    args: &[ArgMaybeAnnotated],
    out_annot: &Option<Rc<AstType>>,
    body: &Rc<Expr>,
) -> TypeVar {
    // body scope
    let polyvar_scope = polyvar_scope.new_scope();

    // arguments
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(ctx, arg.node());
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(ctx, arg_annot.node());
                    let arg_annot = ast_type_to_typevar(ctx, arg_annot.clone());
                    constrain(ctx, ty_annot.clone(), arg_annot.clone());
                    polyvar_scope.add_polys(&arg_annot);
                    generate_constraints_fn_arg(Mode::Ana { expected: ty_annot }, arg.clone(), ctx)
                }
                None => generate_constraints_fn_arg(Mode::Syn, arg.clone(), ctx),
            }
            ty_pat
        })
        .collect();

    // body
    ctx.func_ret_stack.push(Prov::FuncOut(node.clone()));
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node.clone()));
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
    ctx.func_ret_stack.pop();

    TypeVar::make_func(ty_args, ty_body, Reason::Node(node.clone()))
}

fn generate_constraints_func_decl(
    ctx: &mut StaticsContext,
    node: AstNode,
    polyvar_scope: PolyvarScope,
    args: &[ArgMaybeAnnotated],
    out_annot: &Option<Rc<AstType>>,
) {
    // arguments
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(ctx, arg.node());
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(ctx, arg_annot.node());
                    let arg_annot = ast_type_to_typevar(ctx, arg_annot.clone());
                    constrain(ctx, ty_annot.clone(), arg_annot.clone());
                    polyvar_scope.add_polys(&arg_annot);
                    generate_constraints_fn_arg(Mode::Ana { expected: ty_annot }, arg.clone(), ctx)
                }
                None => generate_constraints_fn_arg(Mode::Syn, arg.clone(), ctx),
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node.clone()));

    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_typevar(ctx, out_annot.clone());
        polyvar_scope.add_polys(&out_annot);
        constrain(ctx, ty_body.clone(), out_annot);
    }

    let ty_func = TypeVar::make_func(ty_args, ty_body, Reason::Node(node.clone()));
    let ty_node = TypeVar::from_node(ctx, node);
    constrain(ctx, ty_node, ty_func);
}

fn generate_constraints_func_decl_annotated(
    ctx: &mut StaticsContext,
    node: AstNode,
    polyvar_scope: PolyvarScope,
    args: &[ArgAnnotated],
    out_annot: &Option<Rc<AstType>>,
) {
    // arguments
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(ctx, arg.node());
            let ty_annot = TypeVar::from_node(ctx, arg_annot.node());
            let arg_annot = ast_type_to_typevar(ctx, arg_annot.clone());
            constrain(ctx, ty_annot.clone(), arg_annot.clone());
            polyvar_scope.add_polys(&arg_annot);
            generate_constraints_fn_arg(Mode::Ana { expected: ty_annot }, arg.clone(), ctx);
            ty_pat
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node.clone()));

    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_typevar(ctx, out_annot.clone());
        polyvar_scope.add_polys(&out_annot);
        constrain(ctx, ty_body.clone(), out_annot);
    }

    let ty_func = TypeVar::make_func(ty_args, ty_body, Reason::Node(node.clone()));
    let ty_node = TypeVar::from_node(ctx, node);
    constrain(ctx, ty_node, ty_func);
}

fn generate_constraints_fn_def(
    ctx: &mut StaticsContext,
    polyvar_scope: PolyvarScope,
    f: &FuncDef,
    node: AstNode,
) {
    let ty_func = generate_constraints_func_helper(
        ctx,
        node.clone(),
        polyvar_scope,
        &f.args,
        &f.ret_type,
        &f.body,
    );

    let ty_node = TypeVar::from_node(ctx, node.clone());
    constrain(ctx, ty_node, ty_func.clone());
}

fn generate_constraints_fn_arg(mode: Mode, arg: Rc<Identifier>, ctx: &mut StaticsContext) {
    let ty_arg = TypeVar::from_node(ctx, arg.node());
    match mode {
        Mode::Syn => (),
        Mode::AnaWithReason {
            expected,
            constraint_reason,
        } => {
            constrain_because(ctx, expected, ty_arg.clone(), constraint_reason);
        }
        Mode::Ana { expected } => {
            constrain(ctx, expected, ty_arg.clone());
        }
    };
}

fn generate_constraints_pat(
    polyvar_scope: PolyvarScope,
    mode: Mode,
    pat: Rc<Pat>,
    ctx: &mut StaticsContext,
) {
    let ty_pat = TypeVar::from_node(ctx, pat.node());
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Unit => {
            constrain(ctx, ty_pat, TypeVar::make_unit(Reason::Literal(pat.node())));
        }
        PatKind::Int(_) => {
            constrain(ctx, ty_pat, TypeVar::make_int(Reason::Literal(pat.node())));
        }
        PatKind::Float(_) => {
            constrain(
                ctx,
                ty_pat,
                TypeVar::make_float(Reason::Literal(pat.node())),
            );
        }
        PatKind::Bool(_) => {
            constrain(ctx, ty_pat, TypeVar::make_bool(Reason::Literal(pat.node())));
        }
        PatKind::Str(s) => {
            constrain(
                ctx,
                ty_pat,
                TypeVar::make_string(Reason::Literal(pat.node())),
            );
            ctx.string_constants.insert(s.clone());
        }
        PatKind::Binding(_) => {}
        PatKind::Variant(prefixes, tag, data) => {
            let ty_data = match data {
                Some(data) => TypeVar::from_node(ctx, data.node()),
                None => TypeVar::make_unit(Reason::VariantNoData(pat.node())),
            };

            if !prefixes.is_empty() {
                if let Some(Declaration::EnumVariant { enum_def, variant }) =
                    ctx.resolution_map.get(&tag.id).cloned()
                {
                    let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                        Reason::Node(pat.node()),
                        Nominal::Enum(enum_def.clone()),
                        ctx,
                        pat.node(),
                    );

                    let variant_def = &enum_def.variants[variant as usize];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_unit(Reason::VariantNoData(variant_def.node())),
                        Some(ty) => ast_type_to_typevar(ctx, ty.clone()),
                    };
                    let variant_data_ty = variant_data_ty.subst(&substitution);
                    constrain(ctx, ty_data.clone(), variant_data_ty);

                    constrain(ctx, ty_pat, def_type);

                    if let Some(data) = data {
                        generate_constraints_pat(
                            polyvar_scope,
                            Mode::Ana { expected: ty_data },
                            data.clone(),
                            ctx,
                        )
                    };
                } else {
                    ty_pat.set_flag_missing_info();
                }
            } else {
                // must resolve tag here based on inferred type

                let expected_ty = match mode.clone() {
                    Mode::Syn => None,
                    Mode::AnaWithReason {
                        expected,
                        constraint_reason: _,
                    }
                    | Mode::Ana { expected } => Some(expected),
                };

                let mut can_infer = false;
                if let Some(expected_ty) = expected_ty {
                    if let Some(SolvedType::Nominal(Nominal::Enum(enum_def), _)) =
                        expected_ty.solution()
                    {
                        let mut idx: u16 = 0;
                        for (i, variant) in enum_def.variants.iter().enumerate() {
                            if variant.ctor.v == tag.v {
                                idx = i as u16;
                            }
                        }
                        ctx.resolution_map.insert(
                            tag.id,
                            Declaration::EnumVariant {
                                enum_def: enum_def.clone(),
                                variant: idx,
                            },
                        );
                        can_infer = true;

                        let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                            Reason::Node(pat.node()),
                            Nominal::Enum(enum_def.clone()),
                            ctx,
                            pat.node(),
                        );

                        let variant_def = &enum_def.variants[idx as usize];
                        let variant_data_ty = match &variant_def.data {
                            None => TypeVar::make_unit(Reason::VariantNoData(variant_def.node())),
                            Some(ty) => ast_type_to_typevar(ctx, ty.clone()),
                        };
                        let variant_data_ty = variant_data_ty.subst(&substitution);
                        constrain(ctx, ty_data.clone(), variant_data_ty);

                        constrain(ctx, ty_pat.clone(), def_type);

                        if let Some(data) = data {
                            generate_constraints_pat(
                                polyvar_scope,
                                Mode::Ana { expected: ty_data },
                                data.clone(),
                                ctx,
                            )
                        };
                    }
                }

                if !can_infer {
                    ctx.errors
                        .push(Error::UnqualifiedEnumNeedsAnnotation { node: pat.node() });

                    ty_pat.set_flag_missing_info();
                }
            }
        }
        PatKind::Tuple(pats) => {
            let tys_elements = pats
                .iter()
                .map(|pat| TypeVar::fresh(ctx, Prov::Node(pat.node())))
                .collect();
            constrain(
                ctx,
                ty_pat,
                TypeVar::make_tuple(tys_elements, Reason::Node(pat.node())),
            );
            for pat in pats {
                generate_constraints_pat(polyvar_scope.clone(), Mode::Syn, pat.clone(), ctx)
            }
        }
    }
    let ty_pat = TypeVar::from_node(ctx, pat.node());
    match mode {
        Mode::Syn => (),
        Mode::AnaWithReason {
            expected,
            constraint_reason,
        } => {
            constrain_because(ctx, expected, ty_pat.clone(), constraint_reason);
        }
        Mode::Ana { expected } => {
            constrain(ctx, expected, ty_pat.clone());
        }
    };
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

pub(crate) fn ty_implements_iface(
    ctx: &StaticsContext,
    ty: SolvedType,
    iface: &Rc<InterfaceDecl>,
) -> bool {
    if let SolvedType::Poly(polyty) = &ty {
        let ifaces = resolved_ifaces(ctx, &polyty.iface_names);
        if ifaces.contains(iface) {
            return true;
        }
    }
    let default = vec![];
    let impl_list = ctx.interface_impls.get(iface).unwrap_or(&default);
    let mut found = false;
    for imp in impl_list {
        let impl_ty = ast_type_to_typevar(ctx, imp.typ.clone());
        if let Some(impl_ty) = impl_ty.solution() {
            if ty_fits_impl_ty(ctx, ty.clone(), impl_ty).is_ok() {
                found = true;
            }
        }
    }
    found
}

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
        (SolvedType::Nominal(ident1, tys1), SolvedType::Nominal(ident2, tys2)) => {
            if ident1 == ident2 && tys1.len() == tys2.len() {
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    let SolvedType::Poly(polyty) = ty2.clone() else { panic!() }; // TODO: should this panic be here? Or should an Err be returned?
                    // TODO: gross
                    let ifaces = resolved_ifaces(ctx, &polyty.iface_names);
                    if !ty_fits_impl_ty_poly(ctx, ty1.clone(), &ifaces) {
                        return Err((typ, impl_ty));
                    }
                }
                Ok(())
            } else {
                Err((typ, impl_ty))
            }
        }
        (_, SolvedType::Poly(polyty)) => {
            let ifaces = resolved_ifaces(ctx, &polyty.iface_names);
            if !ty_fits_impl_ty_poly(ctx, typ.clone(), &ifaces) {
                return Err((typ, impl_ty));
            }
            Ok(())
        }
        _ => Err((typ, impl_ty)),
    }
}

// TODO: this logic is clearly wrong. The nested for loops and early returns are a bad choice
fn ty_fits_impl_ty_poly(
    ctx: &StaticsContext,
    typ: SolvedType,
    interfaces: &[Rc<InterfaceDecl>],
) -> bool {
    for interface in interfaces {
        if let SolvedType::Poly(polyty) = &typ {
            let ifaces = resolved_ifaces(ctx, &polyty.iface_names);
            if ifaces.contains(interface) {
                return true;
            }
        }
        if let Some(impl_list) = ctx.interface_impls.get(interface).cloned() {
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

// TODO: memoize this
fn resolved_ifaces(ctx: &StaticsContext, identifiers: &[Rc<Identifier>]) -> Vec<Rc<InterfaceDecl>> {
    identifiers
        .iter()
        .filter_map(|ident| {
            if let Some(Declaration::InterfaceDef(iface)) = ctx.resolution_map.get(&ident.id) {
                Some(iface.clone())
            } else {
                None
            }
        })
        .collect()
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
            PotentialType::Poly(_, decl) => {
                let polyty = &decl.0;
                write!(f, "'{}", polyty.name.v)?;
                if !polyty.iface_names.is_empty() {
                    write!(f, " ")?;
                    for (i, interface) in polyty.iface_names.iter().enumerate() {
                        if i != 0 {
                            write!(f, " + ")?;
                        }
                        write!(f, "{}", interface.v)?;
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
            SolvedType::Poly(polyty) => {
                write!(f, "'{}", polyty.name.v)?;
                if !polyty.iface_names.is_empty() {
                    write!(f, " ")?;
                    for (i, interface) in polyty.iface_names.iter().enumerate() {
                        if i != 0 {
                            write!(f, " + ")?;
                        }
                        write!(f, "{}", interface.v)?;
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
