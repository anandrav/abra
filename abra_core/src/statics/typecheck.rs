/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ast::{
    ArgAnnotated, ArgMaybeAnnotated, AstNode, Expr, ExprKind, FileAst, Identifier, Interface,
    ItemKind, Pat, PatKind, Stmt, StmtKind, Type as AstType, TypeDefKind, TypeKind,
};
use crate::ast::{BinaryOperator, Item};
use crate::builtin::BuiltinOperation;
use crate::environment::Environment;
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt::{self, Display, Write};
use std::rc::Rc;
use utils::hash::HashMap;

use super::{
    Declaration, EnumDef, Error, FuncDef, InterfaceDef, Polytype, StaticsContext, StructDef,
};

pub(crate) fn solve_types(ctx: &mut StaticsContext, file_asts: &Vec<Rc<FileAst>>) {
    // println!("solve_types()");
    for file in file_asts {
        generate_constraints_file_decls(ctx, file.clone());
    }
    // println!("done doing decls");
    for file in file_asts {
        generate_constraints_file_stmts(ctx, file.clone());
    }
    // println!("done doing stmts");
    check_unifvars(ctx);
    // println!("done checking unifvars");
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
                PotentialType::Void(other_provs)
                | PotentialType::Never(other_provs)
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
    Void(Reasons),
    Never(Reasons),
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum SolvedType {
    Poly(Rc<Polytype>), // type name, then list of Interfaces it must match
    Void,
    Never,
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
            Self::Void => Some(Monotype::Void),
            Self::Never => Some(Monotype::Never),
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

    fn key(&self) -> TypeKey {
        match self {
            SolvedType::Poly(poly_decl) => TypeKey::Poly(PolyDeclaration(poly_decl.clone())),
            SolvedType::Void => TypeKey::Void,
            SolvedType::Never => TypeKey::Never,
            SolvedType::Int => TypeKey::Int,
            SolvedType::Float => TypeKey::Float,
            SolvedType::Bool => TypeKey::Bool,
            SolvedType::String => TypeKey::String,
            SolvedType::Function(args, _) => TypeKey::Function(args.len() as u8),
            SolvedType::Tuple(elems) => TypeKey::Tuple(elems.len() as u8),
            SolvedType::Nominal(ident, _) => TypeKey::TyApp(ident.clone()),
        }
    }

    pub(crate) fn is_overloaded(&self) -> bool {
        match self {
            Self::Poly(polyty) => !polyty.interfaces.is_empty(),
            Self::Void => false,
            Self::Never => false,
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
    Void,
    Never,
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
    TyApp(Nominal),
    Void,
    Never,
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
    Node(AstNode), // the type of an expression or statement located at NodeId

    Annotation(AstNode),
    Literal(AstNode),
    Builtin(BuiltinOperation), // a builtin function or constant, which doesn't exist in the AST
    BinopLeft(AstNode),
    BinopRight(AstNode),
    BinopOut(AstNode),
    IndexAccess,
    VariantNoData(AstNode), // the type of the data of a variant with no data, always Void.
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ConstraintReason {
    None,

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
            PotentialType::Void(_) => TypeKey::Void,
            PotentialType::Never(_) => TypeKey::Never,
            PotentialType::Int(_) => TypeKey::Int,
            PotentialType::Float(_) => TypeKey::Float,
            PotentialType::Bool(_) => TypeKey::Bool,
            PotentialType::String(_) => TypeKey::String,
            PotentialType::Function(_, args, _) => TypeKey::Function(args.len() as u8),
            PotentialType::Tuple(_, elems) => TypeKey::Tuple(elems.len() as u8),
            PotentialType::Nominal(_, ident, _) => TypeKey::TyApp(ident.clone()),
        }
    }

    fn solution(&self) -> Option<SolvedType> {
        match self {
            Self::Bool(_) => Some(SolvedType::Bool),
            Self::Int(_) => Some(SolvedType::Int),
            Self::Float(_) => Some(SolvedType::Float),
            Self::String(_) => Some(SolvedType::String),
            Self::Void(_) => Some(SolvedType::Void),
            Self::Never(_) => Some(SolvedType::Never),
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
            | Self::Void(provs)
            | Self::Never(provs)
            | Self::Int(provs)
            | Self::Float(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _)
            | Self::Nominal(provs, _, _) => provs,
        }
    }

    fn make_void(reason: Reason) -> PotentialType {
        PotentialType::Void(reasons_singleton(reason))
    }

    fn make_never(reason: Reason) -> PotentialType {
        PotentialType::Never(reasons_singleton(reason))
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
        ctx: &mut StaticsContext,
        polyvar_scope: PolyvarScope,
        node: AstNode,
    ) -> TypeVar {
        let data = self.0.clone_data();
        if data.types.len() != 1 {
            return self;
        }
        let ty = data.types.into_values().next().unwrap();
        let ty = match ty {
            PotentialType::Void(_)
            | PotentialType::Never(_)
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
                    let mut extension: Vec<(Rc<InterfaceDef>, AstNode)> = Vec::new();
                    for i in &polyty.interfaces {
                        if let Some(Declaration::InterfaceDef(iface)) =
                            ctx.resolution_map.get(&i.name.id)
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
                    .map(|ty| ty.instantiate(ctx, polyvar_scope.clone(), node.clone()))
                    .collect();
                PotentialType::Nominal(provs, ident, params)
            }
            PotentialType::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(ctx, polyvar_scope.clone(), node.clone()))
                    .collect();
                let out = out.instantiate(ctx, polyvar_scope.clone(), node.clone());
                PotentialType::Function(provs, args, out)
            }
            PotentialType::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(ctx, polyvar_scope.clone(), node.clone()))
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
                PotentialType::Void(_)
                | PotentialType::Never(_)
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
                PotentialType::Void(_)
                | PotentialType::Never(_)
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

    pub(crate) fn make_void(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_void(reason))
    }

    pub(crate) fn make_never(reason: Reason) -> TypeVar {
        Self::singleton_solved(PotentialType::make_never(reason))
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
        ctx: &mut StaticsContext,
        reason: Reason,
        nominal: Nominal,
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

// If a variable resolves to some declaration, give its type var.
// For instance, a variable may resolve to a function, so give that function's type.
// Or, a variable may resolve to a variable defined by a let statement.
// Or it may resolve to the name of a struct or an enum variant, in which case its type
// would be the constructor.
fn tyvar_of_variable(
    ctx: &mut StaticsContext,
    decl: &Declaration,
    polyvar_scope: PolyvarScope,
    node: AstNode,
) -> Option<TypeVar> {
    match decl {
        Declaration::FreeFunction(f) => Some(TypeVar::from_node(ctx, f.name.node())),
        Declaration::HostFunction(f) => Some(TypeVar::from_node(ctx, f.name.node())),
        Declaration::_ForeignFunction { f: decl, .. } => {
            Some(TypeVar::from_node(ctx, decl.name.node()))
        }
        Declaration::InterfaceDef(..) => None,
        Declaration::InterfaceMethod {
            i: iface_def,
            method,
        } => Some(TypeVar::from_node(
            ctx,
            iface_def.methods[*method as usize].node(),
        )),
        Declaration::MemberFunction { f: func, .. } => {
            Some(TypeVar::from_node(ctx, func.name.node()))
        }
        Declaration::AssociatedType { .. } => unimplemented!(),
        Declaration::Enum(enum_def) => {
            let (def_type, _) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(node.clone()),
                Nominal::Enum(enum_def.clone()),
                node.clone(),
            );
            Some(def_type)
        }
        Declaration::EnumVariant {
            e: enum_def,
            variant,
        } => {
            let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(node.clone()),
                Nominal::Enum(enum_def.clone()),
                node.clone(),
            );

            let the_variant = &enum_def.variants[*variant as usize];
            match &the_variant.data {
                None => {
                    // TODO: only this path is used. does it make sense to have the dead code below?
                    Some(def_type)
                }
                Some(ty) => {
                    // TODO: this path is never taken by the unit tests.
                    match &*ty.kind {
                        TypeKind::Void => Some(def_type),
                        TypeKind::Tuple(elems) => {
                            let args = elems
                                .iter()
                                .map(|e| {
                                    let e = ast_type_to_typevar(ctx, e.clone());
                                    e.clone().subst(&substitution)
                                })
                                .collect();
                            Some(TypeVar::make_func(
                                args,
                                def_type,
                                Reason::Node(node.clone()),
                            ))
                        }
                        _ => {
                            // TODO: this path is never taken by the unit tests.
                            let ty = ast_type_to_typevar(ctx, ty.clone());
                            Some(TypeVar::make_func(
                                vec![ty.clone().subst(&substitution)],
                                def_type,
                                Reason::Node(node.clone()),
                            ))
                        }
                    }
                }
            }
        }
        Declaration::Struct(struct_def) => {
            let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(node.clone()),
                Nominal::Struct(struct_def.clone()),
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
            Some(TypeVar::make_func(
                fields,
                def_type,
                Reason::Node(node.clone()),
            ))
        }
        Declaration::Array | Declaration::BuiltinType(_) => None,
        Declaration::Polytype(_) => None,
        Declaration::Builtin(builtin) => {
            let ty_signature = builtin.type_signature();
            Some(ty_signature)
        }
        Declaration::Var(node) => {
            let tyvar = TypeVar::from_node(ctx, node.clone());
            // println!("tyvar beforehand is {}", tyvar);
            Some(tyvar)
        }
    }
    .map(|tyvar| tyvar.instantiate(ctx, polyvar_scope, node))
}

// If a type
fn tyvar_of_type_declaration(
    ctx: &mut StaticsContext,
    decl: &Declaration,
    polyvar_scope: PolyvarScope,
    node: AstNode,
) -> Option<TypeVar> {
    match decl {
        Declaration::FreeFunction(f) => Some(TypeVar::from_node(ctx, f.name.node())),
        Declaration::HostFunction(f) => Some(TypeVar::from_node(ctx, f.name.node())),
        Declaration::_ForeignFunction { f: decl, .. } => {
            Some(TypeVar::from_node(ctx, decl.name.node()))
        }
        Declaration::InterfaceDef(..) => None,
        Declaration::InterfaceMethod {
            i: iface_def,
            method,
        } => Some(TypeVar::from_node(
            ctx,
            iface_def.methods[*method as usize].node(),
        )),
        Declaration::MemberFunction { f: func, .. } => {
            Some(TypeVar::from_node(ctx, func.name.node()))
        }
        Declaration::AssociatedType { .. } => unimplemented!(),
        Declaration::Enum(enum_def) => {
            let (def_type, _) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(node.clone()),
                Nominal::Enum(enum_def.clone()),
                node.clone(),
            );
            Some(def_type)
        }
        Declaration::EnumVariant {
            e: enum_def,
            variant,
        } => {
            let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(node.clone()),
                Nominal::Enum(enum_def.clone()),
                node.clone(),
            );

            let the_variant = &enum_def.variants[*variant as usize];
            match &the_variant.data {
                None => {
                    // TODO: only this path is used. does it make sense to have the dead code below?
                    Some(def_type)
                }
                Some(ty) => {
                    // TODO: this path is never taken by the unit tests.
                    match &*ty.kind {
                        TypeKind::Void => Some(def_type),
                        TypeKind::Tuple(elems) => {
                            let args = elems
                                .iter()
                                .map(|e| {
                                    let e = ast_type_to_typevar(ctx, e.clone());
                                    e.clone().subst(&substitution)
                                })
                                .collect();
                            Some(TypeVar::make_func(
                                args,
                                def_type,
                                Reason::Node(node.clone()),
                            ))
                        }
                        _ => {
                            // TODO: this path is never taken by the unit tests.
                            let ty = ast_type_to_typevar(ctx, ty.clone());
                            Some(TypeVar::make_func(
                                vec![ty.clone().subst(&substitution)],
                                def_type,
                                Reason::Node(node.clone()),
                            ))
                        }
                    }
                }
            }
        }
        Declaration::Struct(struct_def) => {
            let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(node.clone()),
                Nominal::Struct(struct_def.clone()),
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
            Some(TypeVar::make_func(
                fields,
                def_type,
                Reason::Node(node.clone()),
            ))
        }
        Declaration::Array | Declaration::BuiltinType(_) => None,
        Declaration::Polytype(_) => None,
        Declaration::Builtin(builtin) => {
            let ty_signature = builtin.type_signature();
            Some(ty_signature)
        }
        Declaration::Var(node) => {
            let tyvar = TypeVar::from_node(ctx, node.clone());
            // println!("tyvar beforehand is {}", tyvar);
            Some(tyvar)
        }
    }
    .map(|tyvar| tyvar.instantiate(ctx, polyvar_scope, node))
}

pub(crate) fn ast_type_to_solved_type(
    ctx: &StaticsContext,
    ast_type: Rc<AstType>,
) -> Option<SolvedType> {
    match &*ast_type.kind {
        TypeKind::Poly(polyty) => Some(SolvedType::Poly(polyty.clone())),
        TypeKind::NamedWithParams(identifier, args) => {
            let sargs = args
                .iter()
                .map(|arg| ast_type_to_solved_type(ctx, arg.clone()))
                .collect::<Option<Vec<_>>>()?;

            let lookup = ctx.resolution_map.get(&identifier.id)?;
            match lookup {
                Declaration::Array => Some(SolvedType::Nominal(Nominal::Array, sargs)),
                Declaration::Struct(struct_def) => Some(SolvedType::Nominal(
                    Nominal::Struct(struct_def.clone()),
                    sargs,
                )),
                Declaration::Enum(enum_def) => {
                    Some(SolvedType::Nominal(Nominal::Enum(enum_def.clone()), sargs))
                }
                _ => None,
            }
        }
        TypeKind::Void => Some(SolvedType::Void),
        TypeKind::Int => Some(SolvedType::Int),
        TypeKind::Float => Some(SolvedType::Float),
        TypeKind::Bool => Some(SolvedType::Bool),
        TypeKind::Str => Some(SolvedType::String),
        TypeKind::Function(args, ret) => {
            let args = args
                .iter()
                .map(|arg| ast_type_to_solved_type(ctx, arg.clone()))
                .collect::<Option<Vec<_>>>()?;

            let ret = ast_type_to_solved_type(ctx, ret.clone())?;
            Some(SolvedType::Function(args, ret.into()))
        }
        TypeKind::Tuple(elems) => {
            let elems = elems
                .iter()
                .map(|elem| ast_type_to_solved_type(ctx, elem.clone()))
                .collect::<Option<Vec<_>>>()?;

            Some(SolvedType::Tuple(elems))
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
                    // println!("gets an empty typevar: {}", ident.v);

                    // since resolution failed, unconstrained type
                    TypeVar::empty()
                }
            }
        }
        TypeKind::Void => TypeVar::make_void(Reason::Annotation(ast_type.node())),
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
            let types = types
                .iter()
                .map(|t| ast_type_to_typevar(ctx, t.clone()))
                .collect();
            TypeVar::make_tuple(types, Reason::Annotation(ast_type.node()))
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
    Ana {
        expected: TypeVar,
    },
    AnaWithReason {
        expected: TypeVar,
        constraint_reason: ConstraintReason,
    },
}

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
    iface: &Rc<InterfaceDef>,
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
        // `never` type does not create conflicts
        if key1 != TypeKey::Never && key2 != TypeKey::Never {
            ctx.errors.push(Error::TypeConflict {
                ty1: potential_ty1,
                ty2: potential_ty2,
                constraint_reason,
            });
        }
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

#[derive(Clone, Debug)]
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
        } else if tyvar.is_underdetermined()
            && let Prov::Node(id) = prov
        {
            ctx.errors
                .push(Error::UnconstrainedUnifvar { node: id.clone() });
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

pub(crate) fn generate_constraints_file_decls(ctx: &mut StaticsContext, file: Rc<FileAst>) {
    for items in file.items.iter() {
        generate_constraints_item_decls(ctx, items.clone());
    }
}

fn generate_constraints_item_decls(ctx: &mut StaticsContext, item: Rc<Item>) {
    match &*item.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(_) => {}
        ItemKind::InterfaceImpl(iface_impl) => {
            let lookup = ctx.resolution_map.get(&iface_impl.iface.id).cloned();
            if let Some(Declaration::InterfaceDef(iface_def)) = &lookup {
                for method in &iface_def.methods {
                    let node_ty = TypeVar::from_node(ctx, method.node());
                    if node_ty.is_locked() {
                        // Interface declaration method types have already been computed.
                        break;
                    }
                    let ty_annot = ast_type_to_typevar(ctx, method.ty.clone());
                    constrain(ctx, node_ty.clone(), ty_annot.clone());
                    // println!("node_ty: {}", node_ty);
                }

                let impl_list = ctx.interface_impls.entry(iface_def.clone()).or_default();
                impl_list.push(iface_impl.clone());

                // BELOW IS WHAT WAS MOVED
                let impl_ty = ast_type_to_typevar(ctx, iface_impl.typ.clone());
                if impl_ty.is_instantiated_nominal() {
                    ctx.errors.push(Error::InterfaceImplTypeNotGeneric {
                        node: iface_impl.typ.node(),
                    })
                }
                let polyvar_scope = PolyvarScope::empty();
                // dbg!(&iface_impl.typ);
                polyvar_scope.add_polys(&impl_ty);
                // dbg!(&polyvar_scope);

                for f in &iface_impl.methods {
                    let method_name = f.name.v.clone();
                    if let Some(interface_method) =
                        iface_def.methods.iter().find(|m| m.name.v == method_name)
                    {
                        let interface_method_ty =
                            ast_type_to_typevar(ctx, interface_method.ty.clone());
                        let actual = TypeVar::from_node(ctx, interface_method.node());
                        // println!("interface_method_ty: {}", interface_method_ty);
                        // println!("actual: {}", actual);
                        constrain(ctx, interface_method_ty.clone(), actual);

                        let mut substitution: Substitution = HashMap::default();
                        if let Some(poly_decl) =
                            interface_method_ty.clone().get_first_polymorphic_type()
                        {
                            substitution.insert(poly_decl, impl_ty.clone());
                        }

                        let expected = interface_method_ty.clone().subst(&substitution);

                        let actual = TypeVar::from_node(ctx, f.name.node());
                        constrain(ctx, expected.clone(), actual);
                        // println!("(1) method {}: {}", method_name, expected);

                        generate_constraints_func_decl(
                            ctx,
                            f.name.node(),
                            polyvar_scope.clone(),
                            &f.args,
                            &f.ret_type,
                        );
                        // println!("(2) method {}: {}", method_name, expected);
                    }
                }
            }
        }
        ItemKind::Extension(ext) => {
            // TODO: LAST HERE
            for f in &ext.methods {
                let err = |ctx: &mut StaticsContext| {
                    ctx.errors
                        .push(Error::MemberFunctionMissingFirstSelfArgument {
                            node: f.name.node(),
                        });
                };
                if let Some((first_arg_identifier, _)) = f.args.first() {
                    if first_arg_identifier.v == "self" {
                        let nominal_ty = ast_type_to_typevar(ctx, ext.typ.clone());
                        let ty_arg = TypeVar::from_node(ctx, first_arg_identifier.node());
                        constrain(ctx, ty_arg, nominal_ty);

                        generate_constraints_func_decl(
                            ctx,
                            f.name.node(),
                            PolyvarScope::empty(),
                            &f.args,
                            &f.ret_type,
                        );
                    } else {
                        err(ctx);
                    }
                } else {
                    err(ctx);
                }
            }
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

pub(crate) fn generate_constraints_file_stmts(ctx: &mut StaticsContext, file: Rc<FileAst>) {
    for items in file.items.iter() {
        generate_constraints_item_stmts(ctx, Mode::Syn, items.clone());
    }
}

fn generate_constraints_item_stmts(ctx: &mut StaticsContext, mode: Mode, item: Rc<Item>) {
    match &*item.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(stmt) => {
            generate_constraints_stmt(ctx, PolyvarScope::empty(), mode, stmt.clone())
        }
        ItemKind::InterfaceImpl(iface_impl) => {
            let impl_ty = ast_type_to_typevar(ctx, iface_impl.typ.clone());
            if impl_ty.is_instantiated_nominal() {
                return;
            }
            let polyvar_scope = PolyvarScope::empty();
            // dbg!(&iface_impl.typ);
            polyvar_scope.add_polys(&impl_ty);

            for f in &iface_impl.methods {
                generate_constraints_fn_def(ctx, polyvar_scope.clone(), f, f.name.node());
            }
        }
        ItemKind::Extension(ext) => {
            for f in &ext.methods {
                if f.args.first().is_some_and(|p| p.0.v == "self") {
                    let ty_func = generate_constraints_func_helper(
                        ctx,
                        f.name.node(),
                        PolyvarScope::empty(),
                        &f.args,
                        &f.ret_type,
                        &f.body,
                    );

                    let ty_node = TypeVar::from_node(ctx, f.name.node());
                    constrain(ctx, ty_node.clone(), ty_func.clone());
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
    ctx: &mut StaticsContext,
    polyvar_scope: PolyvarScope,
    mode: Mode,
    stmt: Rc<Stmt>,
) {
    match &*stmt.kind {
        StmtKind::Expr(expr) => {
            generate_constraints_expr(ctx, polyvar_scope, mode, expr.clone());
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            let ty_pat = TypeVar::from_node(ctx, pat.node());

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_typevar(ctx, ty_ann.clone());

                generate_constraints_pat(
                    ctx,
                    polyvar_scope.clone(),
                    Mode::AnaWithReason {
                        expected: ty_ann,
                        constraint_reason: ConstraintReason::LetStmtAnnotation,
                    },
                    pat.clone(),
                )
            } else {
                generate_constraints_pat(ctx, polyvar_scope.clone(), Mode::Syn, pat.clone())
            };

            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: ty_pat,
                    constraint_reason: ConstraintReason::LetSetLhsRhs,
                },
                expr.clone(),
            );
        }
        StmtKind::Set(lhs, rhs) => {
            let ty_lhs = TypeVar::from_node(ctx, lhs.node());
            generate_constraints_expr(ctx, polyvar_scope.clone(), Mode::Syn, lhs.clone());
            generate_constraints_expr(
                ctx,
                polyvar_scope,
                Mode::AnaWithReason {
                    expected: ty_lhs,
                    constraint_reason: ConstraintReason::LetSetLhsRhs,
                },
                rhs.clone(),
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
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, expr.clone());
            let enclosing_func_ret = ctx.func_ret_stack.last();
            match enclosing_func_ret {
                Some(prov) => {
                    let ret_ty = TypeVar::fresh(ctx, prov.clone());
                    constrain_because(ctx, expr_ty, ret_ty, ConstraintReason::ReturnValue);
                }
                None => {
                    ctx.errors.push(Error::CantReturnHere { node: stmt.node() });
                }
            }
        }
        StmtKind::If(cond, body) => {
            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.node())),
                    constraint_reason: ConstraintReason::Condition,
                },
                cond.clone(),
            );
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, body.clone());
        }
        StmtKind::WhileLoop(cond, expr) => {
            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.node())),
                    constraint_reason: ConstraintReason::Condition,
                },
                cond.clone(),
            );
            ctx.loop_stack.push(Some(expr.id));
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, expr.clone());
            ctx.loop_stack.pop();
        }
    }
}

fn generate_constraints_expr(
    ctx: &mut StaticsContext,
    polyvar_scope: PolyvarScope,
    mode: Mode,
    expr: Rc<Expr>,
) {
    let node_ty = TypeVar::from_node(ctx, expr.node());
    match &*expr.kind {
        ExprKind::Void => {
            constrain(
                ctx,
                node_ty,
                TypeVar::make_void(Reason::Literal(expr.node())),
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
                    ctx,
                    polyvar_scope.clone(),
                    Mode::Ana {
                        expected: elem_ty.clone(),
                    },
                    expr.clone(),
                );
            }
        }
        ExprKind::Variable(_) => {
            let lookup = ctx.resolution_map.get(&expr.id).cloned();
            if let Some(res) = lookup
                && let Some(typ) = tyvar_of_variable(ctx, &res, polyvar_scope.clone(), expr.node())
            {
                // println!("node_ty: {}, typ: {}", node_ty, typ);
                constrain(ctx, typ, node_ty.clone());
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let ty_left = TypeVar::from_node(ctx, left.node());
            let ty_right = TypeVar::from_node(ctx, right.node());
            generate_constraints_expr(ctx, polyvar_scope.clone(), Mode::Syn, left.clone());
            generate_constraints_expr(ctx, polyvar_scope.clone(), Mode::Syn, right.clone());
            let ty_out = node_ty;

            let num_iface_def = ctx.root_namespace.get_declaration("prelude.Num").unwrap();
            let Declaration::InterfaceDef(num_iface) = num_iface_def else { unreachable!() };

            let equal_iface_def = ctx.root_namespace.get_declaration("prelude.Equal").unwrap();
            let Declaration::InterfaceDef(equal_iface) = equal_iface_def else { unreachable!() };

            let tostring_iface_def = ctx
                .root_namespace
                .get_declaration("prelude.ToString")
                .unwrap();
            let Declaration::InterfaceDef(tostring_iface) = tostring_iface_def else {
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
                constrain(ctx, node_ty, TypeVar::make_void(Reason::Node(expr.node())));
                return;
            }
            for statement in statements[..statements.len() - 1].iter() {
                generate_constraints_stmt(ctx, polyvar_scope.clone(), Mode::Syn, statement.clone());
            }
            // if last statement is an expression, the block will have that expression's type
            if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().kind {
                generate_constraints_expr(
                    ctx,
                    polyvar_scope,
                    Mode::Ana { expected: node_ty },
                    terminal_expr.clone(),
                )
            } else if let StmtKind::Return(_) = &*statements.last().unwrap().kind {
                generate_constraints_stmt(
                    ctx,
                    polyvar_scope.clone(),
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                );
                constrain(ctx, node_ty, TypeVar::make_never(Reason::Node(expr.node())))
            } else {
                generate_constraints_stmt(
                    ctx,
                    polyvar_scope,
                    Mode::Syn,
                    statements.last().unwrap().clone(),
                );
                constrain(ctx, node_ty, TypeVar::make_void(Reason::Node(expr.node())))
            }
        }
        ExprKind::IfElse(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.node())),
                    constraint_reason: ConstraintReason::Condition,
                },
                cond.clone(),
            );

            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::Ana {
                    expected: node_ty.clone(),
                },
                expr1.clone(),
            );
            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: node_ty.clone(),
                    constraint_reason: ConstraintReason::IfElseBodies,
                },
                expr2.clone(),
            );
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = TypeVar::from_node(ctx, scrut.node());
            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::Ana {
                    expected: ty_scrutiny.clone(),
                },
                scrut.clone(),
            );
            for arm in arms {
                generate_constraints_pat(
                    ctx,
                    polyvar_scope.clone(),
                    Mode::AnaWithReason {
                        expected: ty_scrutiny.clone(),
                        constraint_reason: ConstraintReason::MatchScrutinyAndPattern,
                    },
                    arm.pat.clone(),
                );
                generate_constraints_stmt(
                    ctx,
                    polyvar_scope.clone(),
                    Mode::Ana {
                        expected: node_ty.clone(),
                    },
                    arm.stmt.clone(),
                );
                if let StmtKind::Expr(..) = &*arm.stmt.kind {
                } else {
                    constrain(
                        ctx,
                        node_ty.clone(),
                        TypeVar::make_void(Reason::Node(expr.node())),
                    )
                }
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
                generate_constraints_expr(ctx, polyvar_scope.clone(), Mode::Syn, expr.clone());
            }
        }
        ExprKind::FuncAp(func, args) => {
            generate_constraints_expr(ctx, polyvar_scope.clone(), Mode::Syn, func.clone());

            generate_constraints_expr_funcap_helper(
                ctx,
                polyvar_scope.clone(),
                args.iter().cloned(),
                func.node(),
                expr.node(),
                node_ty,
            );
        }
        ExprKind::MemberFuncAp(receiver_expr, fname, args) => {
            let receiver_is_namespace = matches!(
                ctx.resolution_map.get(&receiver_expr.id),
                Some(Declaration::Struct(_))
                    | Some(Declaration::Enum(_))
                    | Some(Declaration::Array)
                    | Some(Declaration::InterfaceDef(_))
            );
            match ctx.resolution_map.get(&fname.id).cloned() {
                Some(Declaration::EnumVariant {
                    e: ref enum_def, ..
                }) => {
                    // qualified enum variant
                    // example: list.cons(5, nil)
                    //          ^^^^^^^^^
                    let (tyvar_from_enum, _) = TypeVar::make_nominal_with_substitution(
                        ctx,
                        Reason::Node(receiver_expr.node()),
                        Nominal::Enum(enum_def.clone()),
                        receiver_expr.node(),
                    );
                    constrain(ctx, node_ty.clone(), tyvar_from_enum.clone());

                    generate_constraints_expr_funcap_helper(
                        ctx,
                        polyvar_scope.clone(),
                        std::iter::once(receiver_expr).chain(args).cloned(),
                        fname.node(),
                        expr.node(),
                        node_ty.clone(),
                    );
                }
                Some(ref decl @ Declaration::InterfaceMethod { .. })
                | Some(ref decl @ Declaration::MemberFunction { .. })
                    if receiver_is_namespace =>
                {
                    // fully qualified interface/struct/enum method
                    // example: Clone.clone(my_struct)
                    //          ^^^^^
                    let fn_node_ty = TypeVar::from_node(ctx, fname.node());
                    if let Some(tyvar_from_iface_method) =
                        tyvar_of_variable(ctx, decl, polyvar_scope.clone(), fname.node())
                    {
                        constrain(ctx, fn_node_ty, tyvar_from_iface_method.clone());
                    }

                    generate_constraints_expr_funcap_helper(
                        ctx,
                        polyvar_scope.clone(),
                        args.iter().cloned(),
                        fname.node(),
                        expr.node(),
                        node_ty.clone(),
                    );
                }
                _ => {
                    // potentially a member function call.
                    // Attempt to perform type-directed resolution
                    // example: arr.push(6)
                    //          ^^^^^^^^type is `array`, therefore member function is `array.push`
                    generate_constraints_expr(
                        ctx,
                        polyvar_scope.clone(),
                        Mode::Syn,
                        receiver_expr.clone(),
                    );

                    let failed_to_resolve_member_function = |ctx: &mut StaticsContext, ty| {
                        // failed to resolve member function
                        ctx.errors.push(Error::UnresolvedMemberFunction {
                            node: fname.node(),
                            ty,
                        });

                        node_ty.set_flag_missing_info();
                    };

                    if let Some(solved_ty) =
                        TypeVar::from_node(ctx, receiver_expr.node()).solution()
                    {
                        let ty_key = solved_ty.key();

                        if let Some(memfn_decl) = ctx
                            .member_functions
                            .get(&(ty_key, fname.v.clone()))
                            .cloned()
                        {
                            // TODO: the following block of code is strange and hard to read
                            // it's basically creating the type of the member function using
                            // the member function declaration, then constraining that to the
                            // type of the AST node for the identifier in this MemberFuncAp
                            ctx.resolution_map.insert(fname.id, memfn_decl.clone());
                            let memfn_node_ty = TypeVar::from_node(ctx, fname.node());
                            if let Some(memfn_decl_ty) = tyvar_of_variable(
                                ctx,
                                &memfn_decl,
                                polyvar_scope.clone(),
                                fname.node(),
                            ) {
                                constrain(ctx, memfn_node_ty.clone(), memfn_decl_ty);
                            }
                            println!(
                                "receiver ty: {}",
                                TypeVar::from_node(ctx, receiver_expr.node())
                            );
                            println!("memfn ty before analysis: {}", memfn_node_ty);

                            generate_constraints_expr_funcap_helper(
                                ctx,
                                polyvar_scope.clone(),
                                std::iter::once(receiver_expr).chain(args).cloned(),
                                fname.node(),
                                expr.node(),
                                node_ty.clone(),
                            );
                            println!("memfn ty after analysis: {}", memfn_node_ty);

                            println!("overall node_ty is {}", node_ty);
                        } else {
                            failed_to_resolve_member_function(ctx, solved_ty);
                        }
                    } else {
                        // failed to resolve member function
                        ctx.errors
                            .push(Error::MemberAccessNeedsAnnotation { node: fname.node() });
                        // println!(
                        //     "not solved??: {}",
                        //     TypeVar::from_node(ctx, receiver_expr.node())
                        // );

                        node_ty.set_flag_missing_info();
                    }
                }
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
                // qualified enum with no associated data
                if let Some(ty_of_declaration) =
                    tyvar_of_variable(ctx, decl, polyvar_scope.clone(), expr.node())
                {
                    constrain(ctx, node_ty, ty_of_declaration);
                }
            } else {
                // struct field access
                generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, expr.clone());
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
        ExprKind::MemberAccessLeadingDot(ident) => {
            let expected_ty = match mode.clone() {
                Mode::Syn => None,
                Mode::AnaWithReason {
                    expected,
                    constraint_reason: _,
                }
                | Mode::Ana { expected } => Some(expected),
            };

            let mut can_infer = false;
            if let Some(expected_ty) = expected_ty
                && let Some(SolvedType::Nominal(Nominal::Enum(enum_def), _)) =
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
                        e: enum_def.clone(),
                        variant: idx,
                    },
                );

                let enum_ty = tyvar_of_variable(
                    ctx,
                    &Declaration::Enum(enum_def),
                    polyvar_scope.clone(),
                    expr.node(),
                )
                .unwrap();

                constrain(ctx, node_ty.clone(), enum_ty);
            }

            if !can_infer {
                ctx.errors
                    .push(Error::UnqualifiedEnumNeedsAnnotation { node: expr.node() });

                node_ty.set_flag_missing_info();
            }
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(ctx, polyvar_scope.clone(), Mode::Syn, accessed.clone());

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
                ctx,
                polyvar_scope,
                Mode::AnaWithReason {
                    expected: TypeVar::make_int(Reason::IndexAccess),
                    constraint_reason: ConstraintReason::IndexAccess,
                },
                index.clone(),
            );

            constrain(ctx, node_ty, elem_ty);
        }
        ExprKind::Unwrap(expr) => {
            let Declaration::Enum(maybe_def) =
                ctx.root_namespace.get_declaration("prelude.maybe").unwrap()
            else {
                unreachable!()
            };
            let y_poly_decl = PolyDeclaration(maybe_def.ty_args[0].clone());
            let (maybe_ty, substitution) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(expr.node()),
                Nominal::Enum(maybe_def),
                expr.node(),
            );
            let yes_ty = substitution[&y_poly_decl].clone();

            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::Ana { expected: maybe_ty },
                expr.clone(),
            );

            constrain(ctx, node_ty, yes_ty);
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

fn generate_constraints_expr_funcap_helper(
    ctx: &mut StaticsContext,
    polyvar_scope: PolyvarScope,
    args: impl Iterator<Item = Rc<Expr>>,
    func_node: AstNode,
    expr_node: AstNode,
    node_ty: TypeVar,
) {
    let ty_func = TypeVar::from_node(ctx, func_node.clone());

    // arguments
    let tys_args: Vec<TypeVar> = args
        .enumerate()
        .map(|(n, arg)| {
            let unknown = TypeVar::fresh(ctx, Prov::FuncArg(func_node.clone(), n as u8));

            generate_constraints_expr(
                ctx,
                polyvar_scope.clone(),
                Mode::Ana {
                    expected: unknown.clone(),
                },
                arg.clone(),
            );
            unknown
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(func_node));
    constrain(ctx, ty_body.clone(), node_ty);

    // function type
    let ty_args_and_body = TypeVar::make_func(tys_args, ty_body, Reason::Node(expr_node.clone()));

    constrain_because(
        ctx,
        ty_args_and_body.clone(),
        ty_func.clone(),
        ConstraintReason::FuncCall(expr_node),
    );
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
                    generate_constraints_fn_arg(ctx, Mode::Ana { expected: ty_annot }, arg.clone())
                }
                None => generate_constraints_fn_arg(ctx, Mode::Syn, arg.clone()),
            }
            ty_pat
        })
        .collect();

    // body
    ctx.func_ret_stack.push(Prov::FuncOut(node.clone()));
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node.clone()));
    generate_constraints_expr(
        ctx,
        polyvar_scope.clone(),
        Mode::Ana {
            expected: ty_body.clone(),
        },
        body.clone(),
    );
    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_typevar(ctx, out_annot.clone());
        polyvar_scope.add_polys(&out_annot);
        generate_constraints_expr(
            ctx,
            polyvar_scope,
            Mode::Ana {
                expected: out_annot,
            },
            body.clone(),
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
                    generate_constraints_fn_arg(ctx, Mode::Ana { expected: ty_annot }, arg.clone())
                }
                None => generate_constraints_fn_arg(ctx, Mode::Syn, arg.clone()),
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
            generate_constraints_fn_arg(ctx, Mode::Ana { expected: ty_annot }, arg.clone());
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

fn generate_constraints_fn_arg(ctx: &mut StaticsContext, mode: Mode, arg: Rc<Identifier>) {
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
    ctx: &mut StaticsContext,
    polyvar_scope: PolyvarScope,
    mode: Mode,
    pat: Rc<Pat>,
) {
    let ty_pat = TypeVar::from_node(ctx, pat.node());
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Void => {
            constrain(ctx, ty_pat, TypeVar::make_void(Reason::Literal(pat.node())));
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
                None => TypeVar::make_void(Reason::VariantNoData(pat.node())),
            };

            if !prefixes.is_empty() {
                if let Some(Declaration::EnumVariant {
                    e: enum_def,
                    variant,
                }) = ctx.resolution_map.get(&tag.id).cloned()
                {
                    let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                        ctx,
                        Reason::Node(pat.node()),
                        Nominal::Enum(enum_def.clone()),
                        pat.node(),
                    );

                    let variant_def = &enum_def.variants[variant as usize];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_void(Reason::VariantNoData(variant_def.node())),
                        Some(ty) => ast_type_to_typevar(ctx, ty.clone()),
                    };
                    let variant_data_ty = variant_data_ty.subst(&substitution);
                    constrain(ctx, ty_data.clone(), variant_data_ty);

                    constrain(ctx, ty_pat, def_type);

                    if let Some(data) = data {
                        generate_constraints_pat(
                            ctx,
                            polyvar_scope,
                            Mode::Ana { expected: ty_data },
                            data.clone(),
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
                if let Some(expected_ty) = expected_ty
                    && let Some(SolvedType::Nominal(Nominal::Enum(enum_def), _)) =
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
                            e: enum_def.clone(),
                            variant: idx,
                        },
                    );
                    can_infer = true;

                    let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                        ctx,
                        Reason::Node(pat.node()),
                        Nominal::Enum(enum_def.clone()),
                        pat.node(),
                    );

                    let variant_def = &enum_def.variants[idx as usize];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_void(Reason::VariantNoData(variant_def.node())),
                        Some(ty) => ast_type_to_typevar(ctx, ty.clone()),
                    };
                    let variant_data_ty = variant_data_ty.subst(&substitution);
                    constrain(ctx, ty_data.clone(), variant_data_ty);

                    constrain(ctx, ty_pat.clone(), def_type);

                    if let Some(data) = data {
                        generate_constraints_pat(
                            ctx,
                            polyvar_scope,
                            Mode::Ana { expected: ty_data },
                            data.clone(),
                        )
                    };
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
                generate_constraints_pat(ctx, polyvar_scope.clone(), Mode::Syn, pat.clone())
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
    iface: &Rc<InterfaceDef>,
) -> bool {
    if let SolvedType::Poly(polyty) = &ty {
        let ifaces = resolved_ifaces(ctx, &polyty.interfaces);
        return ifaces.contains(iface);
    }
    let default = vec![];
    let impl_list = ctx.interface_impls.get(iface).unwrap_or(&default);

    impl_list.iter().any(|imp| {
        let impl_ty = ast_type_to_typevar(ctx, imp.typ.clone());
        let Some(impl_ty) = impl_ty.solution() else { return false };
        ty_fits_impl_ty(ctx, ty.clone(), impl_ty)
    })
}

pub(crate) fn ty_fits_impl_ty(ctx: &StaticsContext, typ: SolvedType, impl_ty: SolvedType) -> bool {
    match (&typ, &impl_ty) {
        (SolvedType::Int, SolvedType::Int)
        | (SolvedType::Bool, SolvedType::Bool)
        | (SolvedType::Float, SolvedType::Float)
        | (SolvedType::String, SolvedType::String)
        | (SolvedType::Void, SolvedType::Void) => true,
        (SolvedType::Tuple(tys1), SolvedType::Tuple(tys2)) => {
            tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|(ty1, ty2)| ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone()))
        }
        (SolvedType::Function(args1, out1), SolvedType::Function(args2, out2)) => {
            args1.len() == args2.len()
                && args1
                    .iter()
                    .zip(args2.iter())
                    .all(|(ty1, ty2)| ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone()))
                && ty_fits_impl_ty(ctx, *out1.clone(), *out2.clone())
        }
        (SolvedType::Nominal(ident1, tys1), SolvedType::Nominal(ident2, tys2)) => {
            ident1 == ident2
                && tys1.len() == tys2.len()
                && tys1
                    .iter()
                    .zip(tys2.iter())
                    .all(|(ty1, ty2)| ty_fits_impl_ty(ctx, ty1.clone(), ty2.clone()))
        }
        (_, SolvedType::Poly(polyty)) => {
            let ifaces = resolved_ifaces(ctx, &polyty.interfaces);
            ifaces
                .iter()
                .all(|iface: &Rc<InterfaceDef>| ty_implements_iface(ctx, typ.clone(), iface))
        }
        _ => false,
    }
}

fn resolved_ifaces(ctx: &StaticsContext, identifiers: &[Rc<Interface>]) -> Vec<Rc<InterfaceDef>> {
    identifiers
        .iter()
        .filter_map(|ident| {
            if let Some(Declaration::InterfaceDef(iface)) = ctx.resolution_map.get(&ident.name.id) {
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
            0 => write!(f, "_"),
            1 => write!(f, "{}", types.values().next().unwrap()),
            _ => {
                write!(f, "!{{")?;
                for (i, ty) in types.values().enumerate() {
                    if i > 0 {
                        write!(f, "/ ")?;
                    }
                    write!(f, "{ty}")?;
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
                write!(f, "{}", polyty.name.v)?;
                if !polyty.interfaces.is_empty() {
                    write!(f, " ")?;
                    for (i, interface) in polyty.interfaces.iter().enumerate() {
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
                        write!(f, "{param}")?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", nominal.name())
                }
            }
            PotentialType::Void(_) => write!(f, "void"),
            PotentialType::Never(_) => write!(f, "never"),
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
                    write!(f, "{elem}")?;
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
                write!(f, "{}", polyty.name.v)?;
                if !polyty.interfaces.is_empty() {
                    write!(f, " ")?;
                    for (i, interface) in polyty.interfaces.iter().enumerate() {
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
                        write!(f, "{param}")?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", nominal.name())
                }
            }
            SolvedType::Void => write!(f, "void"),
            SolvedType::Never => write!(f, "never"),
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
                    write!(f, "{elem}")?;
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
                        write!(f, "{param}")?;
                    }
                    write!(f, ">")
                } else {
                    write!(f, "{}", nominal.name())
                }
            }
            Monotype::Void => write!(f, "void"),
            Monotype::Never => write!(f, "never"),
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
                    write!(f, "{elem}")?;
                }
                write!(f, ")")
            }
        }
    }
}
