/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use super::{
    Declaration, EnumDef, Error, FuncDef, FuncResolutionKind, InterfaceArguments, InterfaceDef,
    Polytype, PolytypeDeclaration, StaticsContext, StructDef,
};
use crate::ast::{
    ArgMaybeAnnotated, AstNode, Expr, ExprKind, FileAst, Identifier, Interface, InterfaceImpl,
    InterfaceOutputType, ItemKind, Pat, PatKind, Stmt, StmtKind, Type as AstType, TypeDefKind,
    TypeKind,
};
use crate::ast::{BinaryOperator, Item};
use crate::builtin::BuiltinOperation;
use crate::environment::Environment;
use crate::parse::PrefixOp;
use disjoint_sets::UnionFindNode;
use std::borrow::Borrow;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt::{self, Display, Write};
use std::rc::Rc;
use std::sync::atomic::{AtomicU32, Ordering};
use utils::hash::{HashMap, HashSet};

pub(crate) fn solve_types(ctx: &mut StaticsContext, file_asts: &Vec<Rc<FileAst>>) {
    for file in file_asts {
        generate_constraints_file_decls(ctx, file);
    }
    for file in file_asts {
        generate_constraints_file_stmts(ctx, file);
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
    // if this flag is true, the typevar can't be solved due to an unresolved identifier. Therefore, even if there is only
    //      a single type it was constrained to, it cannot be confidently solved to that type.
    pub(crate) missing_info: bool,

    pub(crate) iface_constraints: InterfaceConstraints,

    // used to uniquely identify TypeVarData and detect if a connected component has already been visited
    // cannot put TypeVarData in a HashSet because it uses interior mutability, but these Ids are fine.
    pub(crate) id: TypeVarDataId,
}

// TODO: make a macro for defining these Id structs and put it in utils.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TypeVarDataId {
    pub(crate) id: u32,
}

impl TypeVarDataId {
    pub(crate) fn new() -> Self {
        static ID_COUNTER: AtomicU32 = AtomicU32::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
}

pub(crate) type InterfaceConstraints = HashMap<InterfaceConstraint, Vec<AstNode>>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InterfaceConstraint {
    iface: Rc<InterfaceDef>,
    args: InterfaceArguments,
}

impl InterfaceConstraint {
    fn new(iface: Rc<InterfaceDef>, args: InterfaceArguments) -> Self {
        Self { iface, args }
    }

    fn no_args(iface: Rc<InterfaceDef>) -> Self {
        Self {
            iface,
            args: vec![],
        }
    }
}

impl TypeVarData {
    fn new() -> Self {
        Self {
            types: HashMap::default(),
            locked: false,
            missing_info: false,
            iface_constraints: HashMap::default(),
            id: TypeVarDataId::new(),
        }
    }

    fn singleton_solved(potential_type: PotentialType) -> Self {
        let mut types = HashMap::default();
        types.insert(potential_type.key(), potential_type);
        Self {
            types,
            locked: true,
            missing_info: false,
            iface_constraints: HashMap::default(),
            id: TypeVarDataId::new(),
        }
    }

    fn solution(&self) -> Option<SolvedType> {
        if self.types.len() == 1 && !self.missing_info {
            self.types.values().next()?.solution()
        } else {
            None
        }
    }

    fn merge_data(first: Self, second: Self) -> Self {
        let mut merged_types = Self {
            types: first.types,
            locked: false,
            missing_info: first.missing_info || second.missing_info,
            iface_constraints: Self::merge_iface_constraints_helper(
                first.iface_constraints,
                second.iface_constraints,
            ),
            id: first.id,
        };
        for (_key, t) in second.types {
            merged_types.extend(t);
        }
        merged_types
    }

    fn merge_iface_constraints_helper(
        mut first: InterfaceConstraints,
        second: InterfaceConstraints,
    ) -> InterfaceConstraints {
        for (iface_constraint, nodes) in second {
            first.entry(iface_constraint).or_default().extend(nodes)
        }
        first
    }

    fn extend(&mut self, t_other: PotentialType) {
        let key = t_other.key();

        // accumulate provenances and constrain children to each other if applicable
        if let Some(t) = self.types.get_mut(&key) {
            match t_other {
                PotentialType::Void(other_reasons)
                | PotentialType::Never(other_reasons)
                | PotentialType::Int(other_reasons)
                | PotentialType::Float(other_reasons)
                | PotentialType::Bool(other_reasons)
                | PotentialType::String(other_reasons) => t.reasons().extend(other_reasons),
                PotentialType::Poly(other_reasons, _) => t.reasons().extend(other_reasons),
                PotentialType::InterfaceOutput(other_reasons, _) => {
                    t.reasons().extend(other_reasons)
                }
                PotentialType::Function(other_reasons, args1, out1) => {
                    t.reasons().extend(other_reasons);
                    if let PotentialType::Function(_, args2, out2) = t {
                        for (arg, arg2) in args1.iter().zip(args2.iter()) {
                            TypeVar::merge(arg, arg2);
                        }
                        TypeVar::merge(&out1, out2);
                    }
                }
                PotentialType::Tuple(other_reasons, elems1) => {
                    t.reasons().extend(other_reasons);
                    if let PotentialType::Tuple(_, elems2) = t {
                        for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                            TypeVar::merge(elem, elem2);
                        }
                    }
                }
                PotentialType::Nominal(other_reasons, _, other_tys) => {
                    let PotentialType::Nominal(_, _, tys) = t else {
                        unreachable!("should be same length")
                    };
                    assert_eq!(tys.len(), other_tys.len());
                    for (ty, other_ty) in tys.iter().zip(other_tys.iter()) {
                        TypeVar::merge(ty, other_ty);
                    }

                    t.reasons().extend(other_reasons);
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
    Poly(Reasons, PolytypeDeclaration),
    InterfaceOutput(Reasons, Rc<InterfaceOutputType>),
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

impl From<PolytypeDeclaration> for Declaration {
    fn from(value: PolytypeDeclaration) -> Self {
        Declaration::Polytype(value)
    }
}

impl From<&PolytypeDeclaration> for Declaration {
    fn from(value: &PolytypeDeclaration) -> Self {
        Declaration::Polytype(value.clone())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum SolvedType {
    Poly(PolytypeDeclaration), // type name, then list of Interfaces it must match
    InterfaceOutput(Rc<InterfaceOutputType>),
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
            Self::InterfaceOutput(_) => None,
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

    // fn key(&self) -> TypeKey {
    //     match self {
    //         SolvedType::Poly(poly_decl) => TypeKey::Poly(poly_decl.clone()),
    //         SolvedType::InterfaceOutput(output_type) => {
    //             TypeKey::InterfaceOutput(output_type.clone())
    //         }
    //         SolvedType::Void => TypeKey::Void,
    //         SolvedType::Never => TypeKey::Never,
    //         SolvedType::Int => TypeKey::Int,
    //         SolvedType::Float => TypeKey::Float,
    //         SolvedType::Bool => TypeKey::Bool,
    //         SolvedType::String => TypeKey::String,
    //         SolvedType::Function(args, _) => TypeKey::Function(args.len() as u8),
    //         SolvedType::Tuple(elems) => TypeKey::Tuple(elems.len() as u8),
    //         SolvedType::Nominal(ident, _) => TypeKey::TyApp(ident.clone()),
    //     }
    // }

    pub(crate) fn is_overloaded(&self) -> bool {
        match self {
            Self::Poly(polyty) => match polyty {
                PolytypeDeclaration::InterfaceSelf(_) => true,
                PolytypeDeclaration::Builtin(_, _) => false, // array_push, array_length, array_pop are not overloaded
                PolytypeDeclaration::Ordinary(p) => !p.interfaces.is_empty(),
            },
            Self::InterfaceOutput(output_type) => !output_type.interfaces.is_empty(),
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
    Poly(PolytypeDeclaration),
    InterfaceOutput(Rc<InterfaceOutputType>),
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
    InstantiatePoly(PolyInstantiationId, PolytypeDeclaration),
    InstantiateInterfaceOutputType(Rc<InterfaceImpl>, Rc<InterfaceOutputType>), // some Interface implementation's instance of an output type
    FuncArg(AstNode, u8), // u8 represents the index of the argument
    FuncOut(AstNode),     // u8 represents how many arguments before this output
    ListElem(AstNode),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct PolyInstantiationId {
    pub(crate) id: u32,
}

impl PolyInstantiationId {
    pub(crate) fn new() -> Self {
        static ID_COUNTER: AtomicU32 = AtomicU32::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
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
    IfWithoutElse(AstNode), // an if-else expression without an else body, always Void (effectively an if statement).
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

type Substitution = HashMap<PolytypeDeclaration, TypeVar>;

impl PotentialType {
    fn key(&self) -> TypeKey {
        match self {
            PotentialType::Poly(_, decl) => TypeKey::Poly(decl.clone()),
            PotentialType::InterfaceOutput(_, output_type) => {
                TypeKey::InterfaceOutput(output_type.clone())
            }
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
            Self::Poly(_, decl) => Some(SolvedType::Poly(decl.clone())),
            Self::InterfaceOutput(_, output_type) => {
                Some(SolvedType::InterfaceOutput(output_type.clone()))
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
            Self::Poly(reasons, _)
            | Self::InterfaceOutput(reasons, _)
            | Self::Void(reasons)
            | Self::Never(reasons)
            | Self::Int(reasons)
            | Self::Float(reasons)
            | Self::Bool(reasons)
            | Self::String(reasons)
            | Self::Function(reasons, _, _)
            | Self::Tuple(reasons, _)
            | Self::Nominal(reasons, _, _) => reasons,
        }
    }

    fn make_void(reason: Reason) -> PotentialType {
        PotentialType::Void(Reasons::single(reason))
    }

    fn make_never(reason: Reason) -> PotentialType {
        PotentialType::Never(Reasons::single(reason))
    }

    fn make_int(reason: Reason) -> PotentialType {
        PotentialType::Int(Reasons::single(reason))
    }

    fn make_float(reason: Reason) -> PotentialType {
        PotentialType::Float(Reasons::single(reason))
    }

    fn make_bool(reason: Reason) -> PotentialType {
        PotentialType::Bool(Reasons::single(reason))
    }

    fn make_string(reason: Reason) -> PotentialType {
        PotentialType::String(Reasons::single(reason))
    }

    pub(crate) fn make_func(args: Vec<TypeVar>, out: TypeVar, reason: Reason) -> PotentialType {
        PotentialType::Function(Reasons::single(reason), args, out)
    }

    fn make_tuple(elems: Vec<TypeVar>, reason: Reason) -> PotentialType {
        PotentialType::Tuple(Reasons::single(reason), elems)
    }

    fn make_poly(reason: Reason, decl: PolytypeDeclaration) -> PotentialType {
        PotentialType::Poly(Reasons::single(reason), decl)
    }

    fn make_iface_output(
        reason: Reason,
        iface_output_type: Rc<InterfaceOutputType>,
    ) -> PotentialType {
        PotentialType::InterfaceOutput(Reasons::single(reason), iface_output_type)
    }

    fn make_nominal(reason: Reason, nominal: Nominal, params: Vec<TypeVar>) -> PotentialType {
        PotentialType::Nominal(Reasons::single(reason), nominal, params)
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

    fn merge(tyvar1: &TypeVar, tyvar2: &TypeVar) {
        let mut tyvar1 = tyvar1.clone();
        let mut tyvar2 = tyvar2.clone();
        tyvar1.0.union_with(&mut tyvar2.0, TypeVarData::merge_data);
    }

    fn merge_iface_constraints(tyvar1: &Self, tyvar2: &Self) {
        let merged_iface_constraints = TypeVarData::merge_iface_constraints_helper(
            tyvar1.0.clone_data().iface_constraints,
            tyvar2.0.clone_data().iface_constraints,
        );
        tyvar1.0.with_data(|d| {
            d.iface_constraints = merged_iface_constraints.clone();
        });
        tyvar2.0.with_data(|d| {
            d.iface_constraints = merged_iface_constraints;
        });
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
        polyvar_scope: &PolyvarScope,
        node: AstNode,
    ) -> TypeVar {
        let id = PolyInstantiationId::new();
        self.instantiate_(ctx, polyvar_scope, node, id)
    }
    fn instantiate_(
        self,
        ctx: &mut StaticsContext,
        polyvar_scope: &PolyvarScope,
        node: AstNode,
        id: PolyInstantiationId,
    ) -> TypeVar {
        let Some(ty) = self.single() else {
            return self;
        };
        let data = self.0.clone_data();
        let ty = match ty {
            PotentialType::Void(_)
            | PotentialType::Never(_)
            | PotentialType::Int(_)
            | PotentialType::Float(_)
            | PotentialType::Bool(_)
            | PotentialType::String(_)
            | PotentialType::InterfaceOutput(..) => {
                ty // noop
            }
            PotentialType::Poly(_, ref decl) => {
                if !polyvar_scope.lookup_poly(decl) {
                    let prov = Prov::InstantiatePoly(id, decl.clone());
                    let ret = TypeVar::fresh(ctx, prov.clone());

                    let ifaces = decl.interfaces(ctx);
                    for constraint in ifaces {
                        constrain_to_iface(ctx, &ret, node.clone(), &constraint);
                    }
                    return ret; // instantiation occurs here
                } else {
                    ty // noop
                }
            }
            PotentialType::Nominal(reasons, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate_(ctx, polyvar_scope, node.clone(), id))
                    .collect();
                PotentialType::Nominal(reasons, ident, params)
            }
            PotentialType::Function(reasons, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate_(ctx, polyvar_scope, node.clone(), id))
                    .collect();
                let out = out.instantiate_(ctx, polyvar_scope, node, id);
                PotentialType::Function(reasons, args, out)
            }
            PotentialType::Tuple(reasons, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate_(ctx, polyvar_scope, node.clone(), id))
                    .collect();
                PotentialType::Tuple(reasons, elems)
            }
        };
        let mut types = HashMap::default();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData {
            types,
            locked: data.locked,
            missing_info: data.missing_info,
            iface_constraints: data.iface_constraints,
            id: data.id,
        };
        TypeVar(UnionFindNode::new(data_instantiated))
    }

    pub(crate) fn get_interface_self_type(&self) -> Option<PolytypeDeclaration> {
        let ty = self.single()?;
        match ty {
            PotentialType::Void(_)
            | PotentialType::Never(_)
            | PotentialType::Int(_)
            | PotentialType::Float(_)
            | PotentialType::Bool(_)
            | PotentialType::String(_)
            | PotentialType::InterfaceOutput(..) => None,
            PotentialType::Poly(_, decl) => match decl {
                PolytypeDeclaration::InterfaceSelf(_) => Some(decl.clone()),
                _ => None,
            },
            PotentialType::Nominal(_, _, params) => {
                for param in &params {
                    if let Some(decl) = param.get_interface_self_type() {
                        return Some(decl);
                    }
                }
                None
            }
            PotentialType::Function(_, args, out) => {
                for arg in &args {
                    if let Some(decl) = arg.get_interface_self_type() {
                        return Some(decl);
                    }
                }
                out.get_interface_self_type()
            }
            PotentialType::Tuple(_, elems) => {
                for elem in &elems {
                    if let Some(decl) = elem.get_interface_self_type() {
                        return Some(decl);
                    }
                }
                None
            }
        }
    }

    pub(crate) fn subst(self, substitution: &Substitution) -> TypeVar {
        let Some(ty) = self.single() else {
            return self;
        };
        let data = self.0.clone_data();

        let ty = match ty {
            PotentialType::Void(_)
            | PotentialType::Never(_)
            | PotentialType::Int(_)
            | PotentialType::Float(_)
            | PotentialType::Bool(_)
            | PotentialType::String(_)
            | PotentialType::InterfaceOutput(..) => {
                ty // noop
            }
            PotentialType::Poly(_, ref decl) => {
                if let Some(new_ty) = substitution.get(decl) {
                    return new_ty.clone(); // substitution occurs here
                } else {
                    ty // noop
                }
            }
            PotentialType::Nominal(reasons, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.subst(substitution))
                    .collect();
                PotentialType::Nominal(reasons, ident, params)
            }
            PotentialType::Function(reasons, args, out) => {
                let args = args.into_iter().map(|ty| ty.subst(substitution)).collect();
                let out = out.subst(substitution);
                PotentialType::Function(reasons, args, out)
            }
            PotentialType::Tuple(reasons, elems) => {
                let elems = elems.into_iter().map(|ty| ty.subst(substitution)).collect();
                PotentialType::Tuple(reasons, elems)
            }
        };
        let mut types = HashMap::default();
        types.insert(ty.key(), ty);
        let new_data = TypeVarData {
            types,
            locked: data.locked,
            missing_info: data.missing_info,
            iface_constraints: data.iface_constraints,
            id: data.id,
        };
        TypeVar(UnionFindNode::new(new_data))
    }

    // Creates a clone of a Type with polymorphic variables not in scope replaced with fresh unifvars
    fn instantiate_iface_output_types(
        self,
        ctx: &mut StaticsContext,
        node: AstNode,
        imp: &Rc<InterfaceImpl>,
    ) -> TypeVar {
        let Some(ty) = self.single() else {
            return self;
        };
        let data = self.0.clone_data();

        let ty = match ty {
            PotentialType::Void(_)
            | PotentialType::Never(_)
            | PotentialType::Int(_)
            | PotentialType::Float(_)
            | PotentialType::Bool(_)
            | PotentialType::String(_)
            | PotentialType::Poly(_, _) => {
                ty // noop
            }
            PotentialType::InterfaceOutput(_, ref output_type) => {
                let prov = Prov::InstantiateInterfaceOutputType(imp.clone(), output_type.clone());
                let ret = TypeVar::fresh(ctx, prov.clone());
                let ifaces = output_type.interfaces(ctx);
                for constraint in &ifaces {
                    constrain_to_iface(ctx, &ret, node.clone(), constraint);
                }
                return ret; // instantiation occurs here
            }
            PotentialType::Nominal(reasons, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate_iface_output_types(ctx, node.clone(), imp))
                    .collect();
                PotentialType::Nominal(reasons, ident, params)
            }
            PotentialType::Function(reasons, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate_iface_output_types(ctx, node.clone(), imp))
                    .collect();
                let out = out.instantiate_iface_output_types(ctx, node, imp);
                PotentialType::Function(reasons, args, out)
            }
            PotentialType::Tuple(reasons, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate_iface_output_types(ctx, node.clone(), imp))
                    .collect();
                PotentialType::Tuple(reasons, elems)
            }
        };
        let mut types = HashMap::default();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData {
            types,
            locked: data.locked,
            missing_info: data.missing_info,
            iface_constraints: data.iface_constraints,
            id: data.id,
        };
        TypeVar(UnionFindNode::new(data_instantiated))
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

    pub(crate) fn make_poly(reason: Reason, decl: PolytypeDeclaration) -> TypeVar {
        Self::singleton_solved(PotentialType::make_poly(reason, decl))
    }

    pub(crate) fn make_iface_output(
        reason: Reason,
        output_type: Rc<InterfaceOutputType>,
    ) -> TypeVar {
        Self::singleton_solved(PotentialType::make_iface_output(reason, output_type))
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
                    substitution.insert(decl.clone(), params[i].clone());
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

impl PolytypeDeclaration {
    fn interfaces(&self, ctx: &StaticsContext) -> Vec<InterfaceConstraint> {
        match self {
            PolytypeDeclaration::InterfaceSelf(iface) => {
                vec![InterfaceConstraint::new(iface.clone(), vec![])]
            }
            PolytypeDeclaration::Builtin(_, _) => vec![],
            PolytypeDeclaration::Ordinary(polyty) => interfaces_helper(ctx, &polyty.interfaces),
        }
    }
}

impl InterfaceOutputType {
    fn interfaces(&self, ctx: &StaticsContext) -> Vec<InterfaceConstraint> {
        interfaces_helper(ctx, &self.interfaces)
    }
}

fn interfaces_helper(
    ctx: &StaticsContext,
    ast_ifaces: &[Rc<Interface>],
) -> Vec<InterfaceConstraint> {
    let mut ifaces = vec![];
    for i in ast_ifaces {
        let Some(Declaration::InterfaceDef(iface)) = ctx.resolution_map.get(&i.name.id) else {
            continue;
        };
        let mut args: InterfaceArguments = vec![];
        for (name, val) in &i.arguments {
            let Some(Declaration::InterfaceOutputType { iface: _, ty: at }) =
                ctx.resolution_map.get(&name.id)
            else {
                continue;
            };
            if let Some(solved_ty) = val.to_solved_type(ctx) {
                args.push((at.clone(), val.clone(), solved_ty));
            }
        }
        ifaces.push(InterfaceConstraint::new(iface.clone(), args));
    }
    ifaces
}

fn tyvar_of_iface_method(
    ctx: &mut StaticsContext,
    iface_def: &Rc<InterfaceDef>,
    method: usize,
    desired_impl_ty: Option<TypeVar>,
    polyvar_scope: &PolyvarScope,
    node: AstNode,
) -> TypeVar {
    if let Some(desired_impl_ty) = desired_impl_ty
        && let Some(desired_impl_ty) = desired_impl_ty.solution()
        && let Some(imp) = desired_impl_ty.get_iface_impls(ctx, iface_def)
    {
        let f = &imp.methods[method];
        return TypeVar::from_node(ctx, f.name.node()).instantiate(ctx, polyvar_scope, node);
    }
    TypeVar::from_node(ctx, iface_def.methods[method].name.node()).instantiate(
        ctx,
        polyvar_scope,
        node,
    )
}

impl AstType {
    pub(crate) fn to_solved_type(self: &Rc<Self>, ctx: &StaticsContext) -> Option<SolvedType> {
        match &*self.kind {
            TypeKind::Poly(polyty) => {
                if let Declaration::Polytype(poly_decl) = ctx.resolution_map.get(&polyty.name.id)? {
                    Some(SolvedType::Poly(poly_decl.clone()))
                } else {
                    None
                }
            }
            TypeKind::NamedWithParams(identifier, args) => {
                let sargs = args
                    .iter()
                    .map(|arg| arg.to_solved_type(ctx))
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
                    Declaration::Polytype(poly_decl) => Some(SolvedType::Poly(poly_decl.clone())),
                    Declaration::InterfaceOutputType { iface: _, ty: at } => {
                        Some(SolvedType::InterfaceOutput(at.clone()))
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
                    .map(|arg| arg.to_solved_type(ctx))
                    .collect::<Option<Vec<_>>>()?;

                let ret = ret.to_solved_type(ctx)?;
                Some(SolvedType::Function(args, ret.into()))
            }
            TypeKind::Tuple(elems) => {
                let elems = elems
                    .iter()
                    .map(|elem| elem.to_solved_type(ctx))
                    .collect::<Option<Vec<_>>>()?;

                Some(SolvedType::Tuple(elems))
            }
        }
    }
}

impl AstType {
    pub(crate) fn to_typevar(self: &Rc<Self>, ctx: &StaticsContext) -> TypeVar {
        let reason = Reason::Annotation(self.node());
        match &*self.kind {
            TypeKind::Poly(polyty) => {
                if let Some(Declaration::Polytype(poly_decl)) =
                    ctx.resolution_map.get(&polyty.name.id)
                {
                    TypeVar::make_poly(reason, poly_decl.clone())
                } else {
                    TypeVar::empty()
                }
            }
            TypeKind::NamedWithParams(ident, params) => {
                let lookup = ctx.resolution_map.get(&ident.id);
                match lookup {
                    Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                        reason,
                        Nominal::Enum(enum_def.clone()),
                        params.iter().map(|param| param.to_typevar(ctx)).collect(),
                    ),

                    Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                        reason,
                        Nominal::Struct(struct_def.clone()),
                        params.iter().map(|param| param.to_typevar(ctx)).collect(),
                    ),
                    Some(Declaration::Array) => TypeVar::make_nominal(
                        reason,
                        Nominal::Array,
                        params.iter().map(|param| param.to_typevar(ctx)).collect(),
                    ),
                    Some(Declaration::Polytype(poly_decl)) => {
                        TypeVar::make_poly(reason, poly_decl.clone())
                    }
                    Some(Declaration::InterfaceOutputType { iface: _, ty: at }) => {
                        TypeVar::make_iface_output(reason, at.clone())
                    }
                    _ => {
                        // since resolution failed, unconstrained type
                        TypeVar::empty()
                    }
                }
            }
            TypeKind::Void => TypeVar::make_void(reason),
            TypeKind::Int => TypeVar::make_int(reason),
            TypeKind::Float => TypeVar::make_float(reason),
            TypeKind::Bool => TypeVar::make_bool(reason),
            TypeKind::Str => TypeVar::make_string(reason),
            TypeKind::Function(lhs, rhs) => TypeVar::make_func(
                lhs.iter().map(|t| t.to_typevar(ctx)).collect(),
                rhs.to_typevar(ctx),
                reason,
            ),
            TypeKind::Tuple(types) => {
                let types = types.iter().map(|t| t.to_typevar(ctx)).collect();
                TypeVar::make_tuple(types, reason)
            }
        }
    }
}

// TODO: this needs a touch up
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) struct Reasons {
    pub(crate) inner: RefCell<BTreeSet<Reason>>,
}

impl Reasons {
    pub(crate) fn single(reason: Reason) -> Reasons {
        let mut set = BTreeSet::new();
        set.insert(reason);
        Self {
            inner: RefCell::new(set),
        }
    }

    pub(crate) fn extend(&self, reasons: Reasons) {
        self.inner
            .borrow_mut()
            .extend(reasons.inner.borrow_mut().iter().cloned());
    }

    pub(crate) fn first(&self) -> Reason {
        self.inner.borrow_mut().first().cloned().unwrap()
    }

    pub(crate) fn len(&self) -> usize {
        self.inner.borrow().len()
    }
}

#[derive(Debug, Clone)]
pub(crate) enum Mode {
    Syn,
    Ana {
        expected: TypeVar,
        constraint_reason: Option<ConstraintReason>,
    },
}

impl Mode {
    fn ana(expected: impl Borrow<TypeVar>) -> Self {
        Mode::Ana {
            expected: expected.borrow().clone(),
            constraint_reason: None,
        }
    }

    fn ana_reason(expected: impl Borrow<TypeVar>, constraint_reason: ConstraintReason) -> Self {
        Mode::Ana {
            expected: expected.borrow().clone(),
            constraint_reason: Some(constraint_reason),
        }
    }

    fn get_expected(&self) -> Option<TypeVar> {
        match self {
            Mode::Syn => None,
            Mode::Ana { expected, .. } => Some(expected.clone()),
        }
    }
}

pub(crate) fn constrain(ctx: &mut StaticsContext, tyvar1: &TypeVar, tyvar2: &TypeVar) {
    constrain_because(ctx, tyvar1, tyvar2, ConstraintReason::None)
}

pub(crate) fn constrain_because(
    ctx: &mut StaticsContext,
    tyvar1: &TypeVar,
    tyvar2: &TypeVar,
    constraint_reason: ConstraintReason,
) {
    match (tyvar1.is_locked(), tyvar2.is_locked()) {
        // Since both TypeVars are already locked, an error is logged if their data do not match
        (true, true) => {
            constrain_locked_typevars(ctx, tyvar1, tyvar2, constraint_reason);
        }
        // Since exactly one of the TypeVars is unsolved, its data will be updated with information from the solved TypeVar
        (false, true) => {
            let potential_ty = tyvar2.single().unwrap();
            tyvar1.0.with_data(|d: &mut TypeVarData| {
                if d.types.is_empty() {
                    assert!(!d.locked);
                    d.locked = true
                }
                d.extend(potential_ty);
            });

            TypeVar::merge_iface_constraints(tyvar1, tyvar2);
        }
        (true, false) => {
            constrain_because(ctx, tyvar2, tyvar1, constraint_reason);
        }
        // Since both TypeVars are unsolved, they are unioned and their data is merged
        (false, false) => {
            TypeVar::merge(tyvar1, tyvar2);
        }
    }
}

pub(crate) fn constrain_to_iface(
    ctx: &mut StaticsContext,
    tyvar: &TypeVar,
    node: AstNode,
    constraint: &InterfaceConstraint,
) {
    if let Some(ty) = tyvar.solution() {
        if !ty.implements_iface(ctx, &constraint.iface) {
            ctx.errors.push(Error::InterfaceNotImplemented {
                ty: ty.clone(),
                iface: constraint.iface.clone(),
                node,
            });
        }
    } else {
        tyvar.0.with_data(|d| {
            d.iface_constraints
                .entry(constraint.clone())
                .or_default()
                .push(node)
        });
    }
}

fn constrain_locked_typevars(
    ctx: &mut StaticsContext,
    tyvar1: &TypeVar,
    tyvar2: &TypeVar,
    constraint_reason: ConstraintReason,
) {
    TypeVar::merge_iface_constraints(tyvar1, tyvar2);

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
                    constrain_because(ctx, arg1, arg2, constraint_reason.clone());
                }
                constrain_because(ctx, &out1, &out2, constraint_reason);
            }
            (PotentialType::Tuple(_, elems1), PotentialType::Tuple(_, elems2)) => {
                for (elem1, elem2) in elems1.iter().zip(elems2.iter()) {
                    constrain_because(ctx, elem1, elem2, constraint_reason.clone());
                }
            }
            (PotentialType::Nominal(_, _, tyvars1), PotentialType::Nominal(_, _, tyvars2)) => {
                for (tyvar1, tyvar2) in tyvars1.iter().zip(tyvars2.iter()) {
                    constrain_because(ctx, tyvar1, tyvar2, constraint_reason.clone());
                }
            }
            _ => {}
        }
    }
}

#[derive(Clone, Debug)]
pub(crate) struct PolyvarScope {
    polyvars_in_scope: Environment<PolytypeDeclaration, ()>,
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

    fn lookup_poly(&self, decl: &PolytypeDeclaration) -> bool {
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
    let mut visited_tyvars = HashSet::default();
    for (prov, tyvar) in ctx.unifvars.clone().iter() {
        let Prov::Node(id) = prov else {
            continue;
        };

        let repr = tyvar.0.find().with_data(|d| d.id);
        if visited_tyvars.contains(&repr) {
            // continue; // TODO: add this back soon!
        }
        visited_tyvars.insert(repr);

        if tyvar.is_conflicted() {
            let type_suggestions = tyvar.clone_types();
            ctx.errors.push(Error::ConflictingUnifvar {
                types: type_suggestions,
            });
        } else if tyvar.is_underdetermined() {
            ctx.errors
                .push(Error::UnconstrainedUnifvar { node: id.clone() });
        } else if let Some(ty) = tyvar.solution() {
            tyvar.0.with_data(|d| {
                for (constraint, nodes) in &d.iface_constraints {
                    let iface = &constraint.iface; // TODO: the args of the iface constraint must be used too
                    if !ty.implements_iface(ctx, iface) {
                        ctx.errors.push(Error::InterfaceNotImplemented {
                            ty: ty.clone(),
                            iface: iface.clone(),
                            node: nodes.first().unwrap().clone(),
                        });
                    }
                }
            });
        }
    }
}

pub(crate) fn generate_constraints_file_decls(ctx: &mut StaticsContext, file: &Rc<FileAst>) {
    for item in file.items.iter() {
        generate_constraints_item_decls0(ctx, item);
    }
    for item in file.items.iter() {
        generate_constraints_item_decls1(ctx, item);
    }
}

fn generate_constraints_item_decls1(ctx: &mut StaticsContext, item: &Rc<Item>) {
    match &*item.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(_) => {}
        ItemKind::InterfaceImpl(iface_impl) => {
            generate_constraints_iface_impl(ctx, iface_impl);
        }
        ItemKind::Extension(_) => {}
        ItemKind::TypeDef(_) => {}
        ItemKind::FuncDef(_) => {}
        ItemKind::FuncDecl { .. } => {}
    }
}

fn generate_constraints_item_decls0(ctx: &mut StaticsContext, item: &Rc<Item>) {
    match &*item.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(_) => {}
        ItemKind::InterfaceImpl(iface_impl) => {
            let lookup = ctx.resolution_map.get(&iface_impl.iface.id).cloned();
            if let Some(Declaration::InterfaceDef(iface_def)) = &lookup {
                let impl_list = ctx.interface_impls.entry(iface_def.clone()).or_default();
                impl_list.push(iface_impl.clone());
            }
        }
        ItemKind::Extension(ext) => {
            for f in &ext.methods {
                let err = |ctx: &mut StaticsContext| {
                    ctx.errors
                        .push(Error::MemberFunctionMissingFirstSelfArgument {
                            node: f.name.node(),
                        });
                };
                if let Some((first_arg_identifier, _)) = f.args.first() {
                    if first_arg_identifier.v == "self" {
                        let nominal_ty = ext.typ.to_typevar(ctx);
                        let ty_arg = TypeVar::from_node(ctx, first_arg_identifier.node());
                        constrain(ctx, &ty_arg, &nominal_ty);

                        generate_constraints_func_decl(
                            ctx,
                            f.name.node(),
                            &f.args,
                            f.ret_type.as_ref(),
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
            TypeDefKind::Enum(..) | TypeDefKind::Struct(..) => {}
        },
        ItemKind::FuncDef(f) => {
            generate_constraints_func_decl(ctx, f.name.node(), &f.args, f.ret_type.as_ref());
        }
        ItemKind::FuncDecl(decl) => {
            generate_constraints_func_decl(ctx, decl.name.node(), &decl.args, Some(&decl.ret_type));
        }
    }
}

fn generate_constraints_iface_impl(ctx: &mut StaticsContext, iface_impl: &Rc<InterfaceImpl>) {
    {
        if !ctx.interface_impl_analyzed.insert(iface_impl.clone()) {
            return;
        }

        let lookup = ctx.resolution_map.get(&iface_impl.iface.id).cloned();
        if let Some(Declaration::InterfaceDef(iface_def)) = &lookup {
            generate_constraints_iface_def(ctx, iface_def);

            // BELOW IS WHAT WAS MOVED
            let impl_ty = iface_impl.typ.to_typevar(ctx);
            if impl_ty.is_instantiated_nominal() {
                ctx.errors.push(Error::InterfaceImplTypeNotGeneric {
                    node: iface_impl.typ.node(),
                })
            }
            let polyvar_scope = PolyvarScope::empty();
            polyvar_scope.add_polys(&impl_ty);

            // ensure typevars for output types are initialized
            for output_ty in &iface_def.output_types {
                let prov =
                    Prov::InstantiateInterfaceOutputType(iface_impl.clone(), output_ty.clone());
                TypeVar::fresh(ctx, prov.clone());
            }

            for f in &iface_impl.methods {
                let method_name = f.name.v.clone();
                if let Some(interface_method) =
                    iface_def.methods.iter().find(|m| m.name.v == method_name)
                {
                    // let interface_method_ty = interface_method.ty.to_typevar(ctx);
                    // let actual = TypeVar::from_node(ctx, interface_method.node());
                    // constrain(ctx, &interface_method_ty, &actual);

                    // let mut substitution: Substitution = HashMap::default();
                    // if let Some(poly_decl) = interface_method_ty.get_interface_self_type() {
                    //     substitution.insert(poly_decl, impl_ty.clone());
                    // }

                    // let expected = interface_method_ty.subst(&substitution);
                    // let expected = expected.instantiate_iface_output_types(
                    //     ctx,
                    //     interface_method.node(),
                    //     iface_impl,
                    // );
                    generate_constraints_func_decl(
                        ctx,
                        interface_method.name.node(),
                        &interface_method.args,
                        Some(&interface_method.ret_type),
                    );
                    let interface_method_ty = TypeVar::from_node(ctx, interface_method.name.node());
                    let mut substitution: Substitution = HashMap::default();
                    if let Some(poly_decl) = interface_method_ty.get_interface_self_type() {
                        substitution.insert(poly_decl, impl_ty.clone());
                    }
                    let expected = interface_method_ty.subst(&substitution);
                    let expected = expected.instantiate_iface_output_types(
                        ctx,
                        interface_method.name.node(),
                        iface_impl,
                    );

                    let actual = TypeVar::from_node(ctx, f.name.node());
                    constrain(ctx, &expected, &actual);

                    generate_constraints_func_decl(
                        ctx,
                        f.name.node(),
                        &f.args,
                        f.ret_type.as_ref(),
                    );

                    constrain_iface_arguments_in_tyvar(
                        ctx,
                        expected,
                        iface_impl,
                        interface_method.name.node(),
                    );
                }
            }
        }
    }
}

fn constrain_iface_arguments_in_tyvar(
    ctx: &mut StaticsContext,
    ty: TypeVar,
    parent_impl: &Rc<InterfaceImpl>,
    iface_method_node: AstNode,
) {
    let d = ty.0.clone_data();
    let Some(potential_ty) = ty.single() else {
        return;
    };
    let Some(solved_ty) = ty.solution() else {
        return;
    };
    for (iface_constraint, _) in d.iface_constraints {
        let Some(imp) = solved_ty.get_iface_impls(ctx, &iface_constraint.iface) else {
            continue;
        };

        for (output_type, val, _) in iface_constraint.args {
            let val = val.to_typevar(ctx);
            let val =
                val.instantiate_iface_output_types(ctx, iface_method_node.clone(), parent_impl);

            generate_constraints_iface_impl(ctx, &imp);

            let prov = Prov::InstantiateInterfaceOutputType(imp.clone(), output_type.clone());
            let output_type_tyvar = TypeVar::fresh(ctx, prov.clone());

            // susbtitute T for U so to speak
            // so if impl's ty is ArrayIterator<U> but the solved_ty is ArrayIterator<T>,
            // the substitution would be { U = T }
            // then call .subst() on the output_type_tyvar
            let subst = get_substitution_of_typ(ctx, &imp.typ, &ty);
            let output_type_tyvar = output_type_tyvar.subst(&subst);

            // constrain that T to tyvar for substitution (which is output type from array Iterable impl)
            constrain(ctx, &output_type_tyvar, &val);
        }
    }
    match potential_ty {
        PotentialType::Void(_)
        | PotentialType::Never(_)
        | PotentialType::Int(_)
        | PotentialType::Float(_)
        | PotentialType::Bool(_)
        | PotentialType::String(_)
        | PotentialType::Poly(_, _)
        | PotentialType::InterfaceOutput(..) => {
            //noop
        }
        PotentialType::Nominal(_, _, params) => {
            params.into_iter().for_each(|ty| {
                constrain_iface_arguments_in_tyvar(
                    ctx,
                    ty.clone(),
                    parent_impl,
                    iface_method_node.clone(),
                )
            });
        }
        PotentialType::Function(_, args, out) => {
            args.into_iter().for_each(|ty| {
                constrain_iface_arguments_in_tyvar(
                    ctx,
                    ty.clone(),
                    parent_impl,
                    iface_method_node.clone(),
                )
            });
            constrain_iface_arguments_in_tyvar(
                ctx,
                out.clone(),
                parent_impl,
                iface_method_node.clone(),
            );
        }
        PotentialType::Tuple(_, elems) => {
            elems.into_iter().for_each(|ty| {
                constrain_iface_arguments_in_tyvar(
                    ctx,
                    ty.clone(),
                    parent_impl,
                    iface_method_node.clone(),
                )
            });
        }
    };
}

fn get_substitution_of_typ(
    ctx: &StaticsContext,
    original: &Rc<AstType>,
    with_params: &TypeVar,
) -> Substitution {
    let mut subst = Substitution::default();
    let Some(potential_ty) = with_params.single() else {
        return subst;
    };
    if let PotentialType::Nominal(_, _, params) = &potential_ty {
        let mut args: Vec<PolytypeDeclaration> = vec![];
        let TypeKind::NamedWithParams(_, imp_args) = &*original.kind else {
            return subst;
        };
        for arg in imp_args {
            let TypeKind::Poly(poly) = &*arg.kind else {
                continue;
            };
            let Some(Declaration::Polytype(poly_decl)) = &ctx.resolution_map.get(&poly.name.id)
            else {
                continue;
            };
            args.push(poly_decl.clone());
        }
        if args.len() != params.len() {
            return subst;
        }
        for (arg, param) in args.iter().zip(params) {
            subst.insert(arg.clone(), param.clone());
        }
    }
    subst
}

fn generate_constraints_iface_def(ctx: &mut StaticsContext, iface_def: &Rc<InterfaceDef>) {
    if !ctx.interface_def_analyzed.insert(iface_def.clone()) {
        return;
    }

    for method in &iface_def.methods {
        let node_ty = TypeVar::from_node(ctx, method.name.node());
        if node_ty.is_locked() {
            // Interface declaration method types have already been computed.
            break;
        }
        generate_constraints_func_decl(
            ctx,
            method.name.node(),
            &method.args,
            Some(&method.ret_type),
        );
    }
}

pub(crate) fn generate_constraints_file_stmts(ctx: &mut StaticsContext, file: &Rc<FileAst>) {
    for items in file.items.iter() {
        generate_constraints_item_stmts(ctx, Mode::Syn, items);
    }
}

fn generate_constraints_item_stmts(ctx: &mut StaticsContext, mode: Mode, item: &Rc<Item>) {
    match &*item.kind {
        ItemKind::InterfaceDef(..) => {}
        ItemKind::Import(..) => {}
        ItemKind::Stmt(stmt) => generate_constraints_stmt(ctx, &PolyvarScope::empty(), mode, stmt),
        ItemKind::InterfaceImpl(iface_impl) => {
            let impl_ty = iface_impl.typ.to_typevar(ctx);
            if impl_ty.is_instantiated_nominal() {
                return;
            }
            let polyvar_scope = PolyvarScope::empty();
            polyvar_scope.add_polys(&impl_ty);

            for f in &iface_impl.methods {
                generate_constraints_func_def(ctx, &polyvar_scope, f, f.name.node());
            }
        }
        ItemKind::Extension(ext) => {
            for f in &ext.methods {
                if f.args.first().is_some_and(|p| p.0.v == "self") {
                    let polyvar_scope = PolyvarScope::empty();
                    let first_arg_ty = TypeVar::from_node(ctx, f.args.first().unwrap().0.node());
                    polyvar_scope.add_polys(&first_arg_ty);
                    generate_constraints_func_def(ctx, &polyvar_scope, f, f.name.node());
                }
            }
        }
        ItemKind::TypeDef(_) => {}
        ItemKind::FuncDef(f) => {
            generate_constraints_func_def(ctx, &PolyvarScope::empty(), f, f.name.node());
        }
        ItemKind::FuncDecl { .. } => {}
    }
}

fn generate_constraints_stmt(
    ctx: &mut StaticsContext,
    polyvar_scope: &PolyvarScope,
    mode: Mode,
    stmt: &Rc<Stmt>,
) {
    match &*stmt.kind {
        StmtKind::Expr(expr) => {
            generate_constraints_expr(ctx, polyvar_scope, mode, expr);
        }
        StmtKind::Let(_mutable, (pat, ty_ann), expr) => {
            let ty_pat = TypeVar::from_node(ctx, pat.node());

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ty_ann.to_typevar(ctx);

                generate_constraints_pat(
                    ctx,
                    Mode::ana_reason(ty_ann, ConstraintReason::LetStmtAnnotation),
                    pat,
                )
            } else {
                generate_constraints_pat(ctx, Mode::Syn, pat)
            };

            generate_constraints_expr(
                ctx,
                polyvar_scope,
                Mode::ana_reason(ty_pat, ConstraintReason::LetSetLhsRhs),
                expr,
            );
        }
        StmtKind::Set(lhs, rhs) => {
            let ty_lhs = TypeVar::from_node(ctx, lhs.node());
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, lhs);
            generate_constraints_expr(
                ctx,
                polyvar_scope,
                Mode::ana_reason(ty_lhs, ConstraintReason::LetSetLhsRhs),
                rhs,
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
            let enclosing_func_ret = ctx.func_ret_stack.last();
            match enclosing_func_ret {
                Some(prov) => {
                    let ret_ty = TypeVar::fresh(ctx, prov.clone());
                    generate_constraints_expr(
                        ctx,
                        polyvar_scope,
                        Mode::ana_reason(ret_ty, ConstraintReason::ReturnValue),
                        expr,
                    );
                }
                None => {
                    ctx.errors.push(Error::CantReturnHere { node: stmt.node() });
                }
            }
        }
        StmtKind::WhileLoop(cond, statements) => {
            generate_constraints_expr(
                ctx,
                polyvar_scope,
                Mode::ana_reason(
                    TypeVar::make_bool(Reason::Node(cond.node())),
                    ConstraintReason::Condition,
                ),
                cond,
            );
            ctx.loop_stack.push(Some(stmt.id));
            for statement in statements.iter() {
                generate_constraints_stmt(ctx, polyvar_scope, Mode::Syn, statement);
            }
            ctx.loop_stack.pop();
        }
        StmtKind::ForLoop(pat, iterable, statements) => {
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, iterable);
            let iterable_ty = TypeVar::from_node(ctx, iterable.node());
            let Some(iterable_ty_solved) = iterable_ty.solution() else {
                ctx.errors.push(Error::Generic {
                    msg: "Cannot typecheck for loop because type of container is not known."
                        .to_string(),
                    node: iterable.node(),
                });
                return;
            };
            let iterable_iface_def = ctx.get_interface_declaration("prelude.Iterable");
            let iterator_iface_def = ctx.get_interface_declaration("prelude.Iterator");
            let Some(imp) = iterable_ty_solved.get_iface_impls(ctx, &iterable_iface_def) else {
                ctx.errors.push(Error::Generic {
                    msg: "For loop container does not implement `Iterable` interface.".to_string(),
                    node: iterable.node(),
                });
                return;
            };
            let output_type = iterable_iface_def
                .output_types
                .iter()
                .find(|ot| ot.name.v == "IterableItem")
                .unwrap();
            let item_ty = ctx
                .unifvars
                .get(&Prov::InstantiateInterfaceOutputType(
                    imp.clone(),
                    output_type.clone(),
                ))
                .unwrap()
                .clone();
            // substitute { T = int } here
            let subst = get_substitution_of_typ(ctx, &imp.typ, &iterable_ty);
            let item_ty = item_ty.subst(&subst);
            generate_constraints_pat(ctx, Mode::ana(item_ty), pat);

            ctx.loop_stack.push(Some(stmt.id));
            for statement in statements.iter() {
                generate_constraints_stmt(ctx, polyvar_scope, Mode::Syn, statement);
            }
            ctx.loop_stack.pop();
            // update bookkeeping for code generation
            // make_iterator type
            let make_iterator_method = imp
                .methods
                .iter()
                .find(|m| m.name.v == "make_iterator")
                .unwrap();
            let make_iterator_type =
                TypeVar::from_node(ctx, make_iterator_method.name.node()).subst(&subst);
            ctx.for_loop_make_iterator_types
                .insert(stmt.id, make_iterator_type.solution().unwrap());

            // Iter::next type
            let iter_output_type = iterable_iface_def
                .output_types
                .iter()
                .find(|ot| ot.name.v == "Iter")
                .unwrap();
            let iter_output_type = ctx
                .unifvars
                .get(&Prov::InstantiateInterfaceOutputType(
                    imp,
                    iter_output_type.clone(),
                ))
                .unwrap()
                .clone();
            let Some(iter_output_type_solved) = iter_output_type.solution() else { panic!() };
            let Some(iterator_imp) =
                iter_output_type_solved.get_iface_impls(ctx, &iterator_iface_def)
            else {
                return;
            };
            let subst2 = get_substitution_of_typ(ctx, &iterator_imp.typ, &iter_output_type);
            let next_method = iterator_imp
                .methods
                .iter()
                .find(|m| m.name.v == "next")
                .unwrap();
            let next_method_typ = TypeVar::from_node(ctx, next_method.name.node());
            let next_method_typ = next_method_typ.subst(&subst2);
            let next_method_typ = next_method_typ.subst(&subst);
            ctx.for_loop_next_types
                .insert(stmt.id, next_method_typ.solution().unwrap());
        }
    }
}

fn generate_constraints_expr(
    ctx: &mut StaticsContext,
    polyvar_scope: &PolyvarScope,
    mode: Mode,
    expr: &Rc<Expr>,
) {
    let node_ty = TypeVar::from_node(ctx, expr.node());
    match &*expr.kind {
        ExprKind::Nil => {
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_void(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Int(_) => {
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_int(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Float(_) => {
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_float(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Bool(_) => {
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_bool(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Str(_) => {
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_string(Reason::Literal(expr.node())),
            );
        }
        ExprKind::Array(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(expr.node()));
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_nominal(
                    Reason::Node(expr.node()),
                    Nominal::Array,
                    vec![elem_ty.clone()],
                ),
            );
            for expr in exprs {
                generate_constraints_expr(ctx, polyvar_scope, Mode::ana(elem_ty.clone()), expr);
            }
        }
        ExprKind::Variable(_) => {
            let lookup = ctx.resolution_map.get(&expr.id).cloned();
            if let Some(decl) = lookup
                && let Some(typ) = match decl {
                    Declaration::Var(node) => {
                        let tyvar = TypeVar::from_node(ctx, node.clone());
                        Some(tyvar)
                    }
                    Declaration::FreeFunction(FuncResolutionKind::Ordinary(func_def)) => {
                        Some(TypeVar::from_node(ctx, func_def.name.node()))
                    }
                    Declaration::FreeFunction(FuncResolutionKind::Host(f)) => {
                        Some(TypeVar::from_node(ctx, f.name.node()))
                    }
                    Declaration::FreeFunction(FuncResolutionKind::_Foreign { decl, .. }) => {
                        Some(TypeVar::from_node(ctx, decl.name.node()))
                    }
                    Declaration::Builtin(builtin) => {
                        let ty_signature = builtin.type_signature();
                        let ty_signature =
                            ty_signature.instantiate(ctx, polyvar_scope, expr.node());
                        Some(ty_signature)
                    }
                    // struct constructor.
                    Declaration::Struct(struct_def) => {
                        let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                            ctx,
                            Reason::Node(expr.node()),
                            Nominal::Struct(struct_def.clone()),
                            expr.node(),
                        );

                        let fields = struct_def
                            .fields
                            .iter()
                            .map(|f| {
                                let ty = f.ty.to_typevar(ctx);
                                ty.subst(&substitution)
                            })
                            .collect();
                        Some(TypeVar::make_func(
                            fields,
                            def_type,
                            Reason::Node(expr.node()),
                        ))
                    }
                    Declaration::InterfaceDef(..)
                    | Declaration::InterfaceOutputType { .. }
                    | Declaration::Enum(_)
                    | Declaration::Array
                    | Declaration::BuiltinType(_)
                    | Declaration::Polytype(_)
                    | Declaration::EnumVariant { .. }
                    | Declaration::InterfaceMethod { .. }
                    | Declaration::MemberFunction { .. } => {
                        // a variable expression should not resolve to the above
                        ctx.errors
                            .push(Error::UnresolvedIdentifier { node: expr.node() });
                        None
                    }
                }
                .map(|tyvar| tyvar.instantiate(ctx, polyvar_scope, expr.node()))
            {
                constrain(ctx, &typ, &node_ty);
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let ty_left = TypeVar::from_node(ctx, left.node());
            let ty_right = TypeVar::from_node(ctx, right.node());
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, left);
            match op {
                BinaryOperator::Equal
                | BinaryOperator::NotEqual
                | BinaryOperator::LessThan
                | BinaryOperator::LessThanOrEqual
                | BinaryOperator::GreaterThan
                | BinaryOperator::GreaterThanOrEqual
                | BinaryOperator::Add
                | BinaryOperator::Subtract
                | BinaryOperator::Multiply
                | BinaryOperator::Divide
                | BinaryOperator::Mod
                | BinaryOperator::Pow => {
                    generate_constraints_expr(
                        ctx,
                        polyvar_scope,
                        Mode::ana_reason(
                            &ty_left,
                            ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                        ),
                        right,
                    );
                }
                BinaryOperator::And | BinaryOperator::Or | BinaryOperator::Format => {
                    generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, right);
                }
            }
            let ty_out = node_ty;

            let num_iface =
                InterfaceConstraint::no_args(ctx.get_interface_declaration("prelude.Num"));
            let equal_iface =
                InterfaceConstraint::no_args(ctx.get_interface_declaration("prelude.Equal"));
            let tostring_iface =
                InterfaceConstraint::no_args(ctx.get_interface_declaration("prelude.ToString"));

            let reason_left = Reason::BinopLeft(expr.node());
            let reason_right = Reason::BinopRight(expr.node());
            let reason_out = Reason::BinopOut(expr.node());
            match op {
                BinaryOperator::And | BinaryOperator::Or => {
                    constrain_because(
                        ctx,
                        &ty_left,
                        &TypeVar::make_bool(reason_left),
                        ConstraintReason::BinaryOperandBool(expr.node()),
                    );
                    constrain_because(
                        ctx,
                        &ty_right,
                        &TypeVar::make_bool(reason_right),
                        ConstraintReason::BinaryOperandBool(expr.node()),
                    );
                    constrain(ctx, &ty_out, &TypeVar::make_bool(reason_out));
                }
                BinaryOperator::Add
                | BinaryOperator::Subtract
                | BinaryOperator::Multiply
                | BinaryOperator::Divide
                | BinaryOperator::Pow => {
                    constrain_to_iface(ctx, &ty_left, left.node(), &num_iface);
                    constrain_to_iface(ctx, &ty_right, right.node(), &num_iface);
                    constrain(ctx, &ty_left, &ty_out);
                }
                BinaryOperator::Mod => {
                    constrain(ctx, &ty_left, &TypeVar::make_int(reason_left));
                    constrain(ctx, &ty_right, &TypeVar::make_int(reason_right));
                    constrain(ctx, &ty_out, &TypeVar::make_int(reason_out));
                }
                BinaryOperator::LessThan
                | BinaryOperator::GreaterThan
                | BinaryOperator::LessThanOrEqual
                | BinaryOperator::GreaterThanOrEqual => {
                    constrain_to_iface(ctx, &ty_left, left.node(), &num_iface);
                    constrain_to_iface(ctx, &ty_right, right.node(), &num_iface);
                    constrain(ctx, &ty_out, &TypeVar::make_bool(reason_out));
                }
                BinaryOperator::Format => {
                    constrain_to_iface(ctx, &ty_left, left.node(), &tostring_iface);
                    constrain_to_iface(ctx, &ty_right, right.node(), &tostring_iface);
                    constrain_because(
                        ctx,
                        &ty_out,
                        &TypeVar::make_string(reason_out),
                        ConstraintReason::BinaryOperandsMustMatch(expr.node()),
                    );
                }
                BinaryOperator::Equal | BinaryOperator::NotEqual => {
                    constrain_to_iface(ctx, &ty_left, left.node(), &equal_iface);
                    constrain_to_iface(ctx, &ty_right, right.node(), &equal_iface);
                    constrain(ctx, &ty_out, &TypeVar::make_bool(reason_out));
                }
            }
        }
        ExprKind::Unop(op, right) => {
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, right);
            let ty_right = TypeVar::from_node(ctx, right.node());
            let ty_out = node_ty;

            let num_iface =
                InterfaceConstraint::no_args(ctx.get_interface_declaration("prelude.Num"));

            match op {
                PrefixOp::Minus => {
                    constrain_to_iface(ctx, &ty_right, right.node(), &num_iface);
                    constrain(ctx, &ty_out, &ty_right);
                }
            }
        }
        ExprKind::Block(statements) => {
            if statements.is_empty() {
                constrain(
                    ctx,
                    &node_ty,
                    &TypeVar::make_void(Reason::Node(expr.node())),
                );
            } else {
                for statement in statements[..statements.len() - 1].iter() {
                    generate_constraints_stmt(ctx, polyvar_scope, Mode::Syn, statement);
                }
                // if last statement is an expression, the block will have that expression's type
                if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().kind {
                    generate_constraints_expr(ctx, polyvar_scope, mode.clone(), terminal_expr);
                    let expr_ty = TypeVar::from_node(ctx, terminal_expr.node());
                    constrain(ctx, &expr_ty, &node_ty);
                } else if let StmtKind::Return(_) = &*statements.last().unwrap().kind {
                    generate_constraints_stmt(
                        ctx,
                        polyvar_scope,
                        mode.clone(),
                        statements.last().unwrap(),
                    );
                    constrain(
                        ctx,
                        &node_ty,
                        &TypeVar::make_never(Reason::Node(expr.node())),
                    )
                } else {
                    generate_constraints_stmt(
                        ctx,
                        polyvar_scope,
                        Mode::Syn,
                        statements.last().unwrap(),
                    );
                    constrain(
                        ctx,
                        &node_ty,
                        &TypeVar::make_void(Reason::Node(expr.node())),
                    )
                }
            }
        }
        ExprKind::IfElse(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx,
                polyvar_scope,
                Mode::ana_reason(
                    TypeVar::make_bool(Reason::Node(cond.node())),
                    ConstraintReason::Condition,
                ),
                cond,
            );

            generate_constraints_expr(ctx, polyvar_scope, mode.clone(), expr1);
            let expr1_ty = TypeVar::from_node(ctx, expr1.node());
            if let Some(expr2) = expr2 {
                generate_constraints_expr(ctx, polyvar_scope, mode.clone(), expr2);
                let expr2_ty = TypeVar::from_node(ctx, expr2.node());
                constrain_because(ctx, &expr1_ty, &expr2_ty, ConstraintReason::IfElseBodies);
                constrain(ctx, &expr2_ty, &node_ty);
                constrain(ctx, &expr1_ty, &node_ty);
            } else {
                constrain(
                    ctx,
                    &node_ty,
                    &TypeVar::make_void(Reason::IfWithoutElse(expr.node())),
                );
            }
        }
        ExprKind::Match(scrut, arms) => {
            let ty_scrutiny = TypeVar::from_node(ctx, scrut.node());
            generate_constraints_expr(ctx, polyvar_scope, Mode::ana(&ty_scrutiny), scrut);
            for arm in arms {
                generate_constraints_pat(
                    ctx,
                    Mode::ana_reason(&ty_scrutiny, ConstraintReason::MatchScrutinyAndPattern),
                    &arm.pat,
                );
                generate_constraints_stmt(ctx, polyvar_scope, Mode::ana(&node_ty), &arm.stmt);
                if let StmtKind::Expr(..) = &*arm.stmt.kind {
                } else {
                    constrain(
                        ctx,
                        &node_ty,
                        &TypeVar::make_void(Reason::Node(expr.node())),
                    )
                }
            }
        }
        ExprKind::AnonymousFunction(args, out_annot, body) => {
            let func_node = expr.node();
            let ty_func = generate_constraints_func_def_helper(
                ctx,
                func_node,
                polyvar_scope,
                args,
                out_annot,
                body,
            );

            constrain(ctx, &node_ty, &ty_func);
        }
        ExprKind::Tuple(exprs) => {
            let tys = exprs
                .iter()
                .map(|expr| TypeVar::fresh(ctx, Prov::Node(expr.node())))
                .collect();
            constrain(
                ctx,
                &node_ty,
                &TypeVar::make_tuple(tys, Reason::Node(expr.node())),
            );
            if let Mode::Ana {
                constraint_reason,
                expected,
            } = &mode
                && let Some(PotentialType::Tuple(_, elems)) = expected.single()
            {
                for (expr, expected) in exprs.iter().zip(elems) {
                    generate_constraints_expr(
                        ctx,
                        polyvar_scope,
                        Mode::Ana {
                            expected,
                            constraint_reason: constraint_reason.clone(),
                        },
                        expr,
                    )
                }
            } else {
                for expr in exprs {
                    generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, expr)
                }
            }
        }
        ExprKind::FuncAp(func, args) => {
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, func);

            generate_constraints_expr_funcap_helper(
                ctx,
                polyvar_scope,
                args,
                func.node(),
                expr.node(),
                node_ty,
            );
        }
        ExprKind::MemberFuncAp(receiver_expr, fname, args) => {
            if let Some(receiver_expr) = receiver_expr {
                let receiver_is_namespace = matches!(
                    ctx.resolution_map.get(&receiver_expr.id),
                    Some(Declaration::Struct(_))
                        | Some(Declaration::Enum(_))
                        | Some(Declaration::Array)
                        | Some(Declaration::InterfaceDef(_))
                );
                match ctx.resolution_map.get(&fname.id).cloned() {
                    Some(Declaration::EnumVariant {
                        e: enum_def,
                        variant,
                    }) => {
                        // qualified enum variant
                        // example: list.cons(5, nil)
                        //          ^^^^^^^^^
                        enum_ctor_helper(
                            ctx,
                            polyvar_scope,
                            &enum_def,
                            variant,
                            args,
                            fname.node(),
                            expr.node(),
                        );
                    }
                    Some(Declaration::InterfaceMethod {
                        iface: iface_def,
                        method,
                    }) => {
                        // fully qualified interface method
                        // example: Clone.clone(my_struct)
                        //          ^^^^^
                        let memfn_node_ty = TypeVar::from_node(ctx, fname.node());
                        let impl_ty = match args.first() {
                            Some(arg) => {
                                generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, arg);
                                Some(TypeVar::from_node(ctx, arg.node()))
                            }
                            None => None,
                        };

                        let memfn_decl_ty = tyvar_of_iface_method(
                            ctx,
                            &iface_def,
                            method,
                            impl_ty,
                            polyvar_scope,
                            fname.node(),
                        );
                        constrain(ctx, &memfn_node_ty, &memfn_decl_ty);

                        generate_constraints_expr_funcap_helper(
                            ctx,
                            polyvar_scope,
                            args,
                            fname.node(),
                            expr.node(),
                            node_ty.clone(),
                        );
                    }
                    Some(Declaration::MemberFunction(func)) if receiver_is_namespace => {
                        // fully qualified struct/enum method
                        // example: Person.fullname(my_person)
                        //          ^^^^^
                        let fn_node_ty = TypeVar::from_node(ctx, fname.node());
                        let memfn_ty = TypeVar::from_node(ctx, func.name.node()).instantiate(
                            ctx,
                            polyvar_scope,
                            fname.node(),
                        );
                        constrain(ctx, &fn_node_ty, &memfn_ty);

                        generate_constraints_expr_funcap_helper(
                            ctx,
                            polyvar_scope,
                            args,
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
                        generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, receiver_expr);

                        if let Some(potential_ty) =
                            TypeVar::from_node(ctx, receiver_expr.node()).single()
                        {
                            let ty_key = potential_ty.key();
                            if let Some(memfn_decl) = ctx
                                .member_functions
                                .get(&(ty_key, fname.v.clone()))
                                .cloned()
                            {
                                ctx.resolution_map.insert(fname.id, memfn_decl.clone());
                                let memfn_node_ty = TypeVar::from_node(ctx, fname.node());
                                match memfn_decl {
                                    // TODO: this only works for ordinary, not host or FFI
                                    Declaration::MemberFunction(func) => {
                                        let memfn_ty = TypeVar::from_node(ctx, func.name.node())
                                            .instantiate(ctx, polyvar_scope, fname.node());
                                        constrain(ctx, &memfn_node_ty, &memfn_ty);
                                    }
                                    Declaration::InterfaceMethod {
                                        iface: iface_def,
                                        method,
                                    } => {
                                        let impl_ty = TypeVar::from_node(ctx, receiver_expr.node());
                                        let memfn_decl_ty = tyvar_of_iface_method(
                                            ctx,
                                            &iface_def,
                                            method,
                                            Some(impl_ty),
                                            polyvar_scope,
                                            fname.node(),
                                        );
                                        constrain(ctx, &memfn_node_ty, &memfn_decl_ty);
                                    }
                                    _ => unreachable!(),
                                }

                                generate_constraints_expr_funcap_helper(
                                    ctx,
                                    polyvar_scope,
                                    &std::iter::once(receiver_expr)
                                        .chain(args)
                                        .cloned()
                                        .collect::<Vec<_>>(),
                                    fname.node(),
                                    expr.node(),
                                    node_ty.clone(),
                                );
                            } else {
                                // failed to resolve member function
                                ctx.errors.push(Error::UnresolvedMemberFunction {
                                    receiver_node: receiver_expr.node(),
                                    memfn_node: fname.node(),
                                    ty: potential_ty,
                                });

                                node_ty.set_flag_missing_info();
                            }
                        } else {
                            // failed to resolve member function
                            ctx.errors
                                .push(Error::MemberAccessNeedsAnnotation { node: fname.node() });

                            node_ty.set_flag_missing_info();
                        }
                    }
                }
            } else {
                // unqualfied enum variant
                // example: .some(3)
                //          ^^^^^^^^^
                if let Some((enum_def, variant)) = infer_enum(&mode, &fname.v) {
                    ctx.resolution_map.insert(
                        fname.id,
                        Declaration::EnumVariant {
                            e: enum_def.clone(),
                            variant,
                        },
                    );

                    enum_ctor_helper(
                        ctx,
                        polyvar_scope,
                        &enum_def,
                        variant,
                        args,
                        fname.node(),
                        expr.node(),
                    );
                } else {
                    ctx.errors
                        .push(Error::UnqualifiedEnumNeedsAnnotation { node: expr.node() });

                    node_ty.set_flag_missing_info();
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
            if let Some(Declaration::EnumVariant {
                e: enum_def,
                variant: _,
            }) = ctx.resolution_map.get(&member_ident.id).cloned()
            {
                // qualified enum with no associated data
                let (def_type, _) = TypeVar::make_nominal_with_substitution(
                    ctx,
                    Reason::Node(expr.node()),
                    Nominal::Enum(enum_def.clone()),
                    expr.node(),
                );
                constrain(ctx, &node_ty, &def_type);
            } else {
                // struct field access
                generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, expr);
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
                            let ty_field = field.ty.to_typevar(ctx);
                            constrain(ctx, &node_ty, &ty_field);
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
            if let Some((enum_def, idx)) = infer_enum(&mode, &ident.v) {
                ctx.resolution_map.insert(
                    ident.id,
                    Declaration::EnumVariant {
                        e: enum_def.clone(),
                        variant: idx,
                    },
                );

                let (enum_ty, _) = TypeVar::make_nominal_with_substitution(
                    ctx,
                    Reason::Node(expr.node()),
                    Nominal::Enum(enum_def.clone()),
                    expr.node(),
                );

                constrain(ctx, &node_ty, &enum_ty);
            } else {
                ctx.errors
                    .push(Error::UnqualifiedEnumNeedsAnnotation { node: expr.node() });

                node_ty.set_flag_missing_info();
            }
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(ctx, polyvar_scope, Mode::Syn, accessed);

            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(accessed.node()));
            let accessed_ty = TypeVar::from_node(ctx, accessed.node());
            constrain(
                ctx,
                &accessed_ty,
                &TypeVar::make_nominal(
                    Reason::Node(accessed.node()),
                    Nominal::Array,
                    vec![elem_ty.clone()],
                ),
            );
            generate_constraints_expr(
                ctx,
                polyvar_scope,
                Mode::ana_reason(
                    TypeVar::make_int(Reason::IndexAccess),
                    ConstraintReason::IndexAccess,
                ),
                index,
            );

            constrain(ctx, &node_ty, &elem_ty);
        }
        ExprKind::Unwrap(expr) => {
            let Declaration::Enum(option_def) = ctx
                .root_namespace
                .get_declaration("prelude.option")
                .unwrap()
            else {
                unreachable!()
            };
            let y_poly_decl = PolytypeDeclaration::Ordinary(option_def.ty_args[0].clone());
            let (option_ty, substitution) = TypeVar::make_nominal_with_substitution(
                ctx,
                Reason::Node(expr.node()),
                Nominal::Enum(option_def),
                expr.node(),
            );
            let yes_ty = substitution[&y_poly_decl].clone();

            generate_constraints_expr(ctx, polyvar_scope, Mode::ana(option_ty), expr);

            constrain(ctx, &node_ty, &yes_ty);
        }
    }
    let node_ty = TypeVar::from_node(ctx, expr.node());
    handle_ana(ctx, mode, node_ty);
}

fn infer_enum(mode: &Mode, variant_name: &str) -> Option<(Rc<EnumDef>, usize)> {
    let expected_ty = mode.get_expected();
    if let Some(expected_ty) = expected_ty
        && let Some(PotentialType::Nominal(_, Nominal::Enum(enum_def), _)) = expected_ty.single()
        && let Some(idx) = enum_def
            .variants
            .iter()
            .position(|v| v.ctor.v == variant_name)
    {
        Some((enum_def, idx))
    } else {
        None
    }
}

fn enum_ctor_helper(
    ctx: &mut StaticsContext,
    polyvar_scope: &PolyvarScope,
    enum_def: &Rc<EnumDef>,
    variant: usize,
    args: &[Rc<Expr>],
    func_node: AstNode,
    funcap_node: AstNode,
) {
    let (def_type, subst) = TypeVar::make_nominal_with_substitution(
        ctx,
        Reason::Node(func_node.clone()),
        Nominal::Enum(enum_def.clone()),
        funcap_node.clone(),
    );
    let node_ty = TypeVar::from_node(ctx, funcap_node.clone());
    constrain(ctx, &node_ty, &def_type);

    let variant = &enum_def.variants[variant];
    let tys_args = match &variant.data {
        None => vec![],
        Some(data) => match &*data.kind {
            TypeKind::Tuple(elems) => elems.iter().map(|e| e.to_typevar(ctx)).collect(),
            _ => {
                vec![data.to_typevar(ctx)]
            }
        },
    };
    let tys_args = tys_args.iter().cloned().map(|t| t.subst(&subst)).collect();
    let func_ty = TypeVar::make_func(tys_args, def_type.clone(), Reason::Node(func_node.clone()));
    let func_node_ty = TypeVar::from_node(ctx, func_node.clone());
    constrain(ctx, &func_ty, &func_node_ty);

    generate_constraints_expr_funcap_helper(
        ctx,
        polyvar_scope,
        args,
        func_node,
        funcap_node,
        def_type.clone(),
    );
}

fn generate_constraints_func_decl(
    ctx: &mut StaticsContext,
    node: AstNode,
    args: &[ArgMaybeAnnotated],
    out_annot: Option<&Rc<AstType>>,
) {
    // arguments
    let ty_args = generate_constraints_func_args(ctx, &PolyvarScope::empty(), args);

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node.clone()));

    if let Some(out_annot) = out_annot {
        let out_annot = out_annot.to_typevar(ctx);
        constrain(ctx, &ty_body, &out_annot);
    }

    let ty_func = TypeVar::make_func(ty_args, ty_body, Reason::Node(node.clone()));
    let ty_node = TypeVar::from_node(ctx, node);
    constrain(ctx, &ty_node, &ty_func);
}

fn generate_constraints_func_def_helper(
    ctx: &mut StaticsContext,
    node: AstNode,
    polyvar_scope: &PolyvarScope,
    args: &[ArgMaybeAnnotated],
    out_annot: &Option<Rc<AstType>>,
    body: &Rc<Expr>,
) -> TypeVar {
    // body scope
    let polyvar_scope = polyvar_scope.new_scope();

    // arguments
    let ty_args = generate_constraints_func_args(ctx, &polyvar_scope, args);

    // body
    ctx.func_ret_stack.push(Prov::FuncOut(node.clone()));
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node.clone()));
    if let Some(out_annot) = out_annot {
        let out_annot = out_annot.to_typevar(ctx);
        polyvar_scope.add_polys(&out_annot);

        generate_constraints_expr(ctx, &polyvar_scope, Mode::ana(&out_annot), body);
        constrain(ctx, &ty_body, &out_annot);
    } else {
        generate_constraints_expr(ctx, &polyvar_scope, Mode::ana(&ty_body), body);
    }
    ctx.func_ret_stack.pop();

    TypeVar::make_func(ty_args, ty_body, Reason::Node(node.clone()))
}

fn generate_constraints_func_def(
    ctx: &mut StaticsContext,
    polyvar_scope: &PolyvarScope,
    f: &FuncDef,
    node: AstNode,
) {
    let ty_func = generate_constraints_func_def_helper(
        ctx,
        node.clone(),
        polyvar_scope,
        &f.args,
        &f.ret_type,
        &f.body,
    );

    let ty_node = TypeVar::from_node(ctx, node.clone());
    constrain(ctx, &ty_node, &ty_func);
}

fn generate_constraints_func_args(
    ctx: &mut StaticsContext,
    polyvar_scope: &PolyvarScope,
    args: &[ArgMaybeAnnotated],
) -> Vec<TypeVar> {
    args.iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = TypeVar::from_node(ctx, arg.node());
            match arg_annot {
                Some(arg_annot) => {
                    let ty_annot = TypeVar::from_node(ctx, arg_annot.node());
                    let arg_annot = arg_annot.to_typevar(ctx);
                    constrain(ctx, &ty_annot, &arg_annot);
                    polyvar_scope.add_polys(&arg_annot);
                    generate_constraints_fn_arg(ctx, Mode::ana(ty_annot), arg)
                }
                None => generate_constraints_fn_arg(ctx, Mode::Syn, arg),
            }
            ty_pat
        })
        .collect()
}

fn generate_constraints_expr_funcap_helper(
    ctx: &mut StaticsContext,
    polyvar_scope: &PolyvarScope,
    args: &[Rc<Expr>],
    func_node: AstNode,
    expr_node: AstNode,
    node_ty: TypeVar,
) {
    let ty_func = TypeVar::from_node(ctx, func_node.clone());

    if let Some(PotentialType::Function(_, func_ty_args, _)) = ty_func.single() {
        args.iter().zip(func_ty_args).for_each(|(arg, expected)| {
            generate_constraints_expr(ctx, polyvar_scope, Mode::ana(expected), arg);
        });
    }

    // arguments
    let tys_args: Vec<TypeVar> = args
        .iter()
        .enumerate()
        .map(|(n, arg)| {
            let unknown = TypeVar::fresh(ctx, Prov::FuncArg(func_node.clone(), n as u8));
            let arg_ty = TypeVar::from_node(ctx, arg.node());
            constrain(ctx, &unknown, &arg_ty);
            unknown
        })
        .collect();

    // body
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(func_node));
    constrain(ctx, &ty_body, &node_ty);

    // function type
    let ty_args_and_body = TypeVar::make_func(tys_args, ty_body, Reason::Node(expr_node.clone()));

    constrain_because(
        ctx,
        &ty_args_and_body,
        &ty_func,
        ConstraintReason::FuncCall(expr_node),
    );
}

fn generate_constraints_fn_arg(ctx: &mut StaticsContext, mode: Mode, arg: &Rc<Identifier>) {
    let ty_arg = TypeVar::from_node(ctx, arg.node());
    handle_ana(ctx, mode, ty_arg);
}

fn generate_constraints_pat(ctx: &mut StaticsContext, mode: Mode, pat: &Rc<Pat>) {
    let ty_pat = TypeVar::from_node(ctx, pat.node());
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Void => {
            constrain(
                ctx,
                &ty_pat,
                &TypeVar::make_void(Reason::Literal(pat.node())),
            );
        }
        PatKind::Int(_) => {
            constrain(
                ctx,
                &ty_pat,
                &TypeVar::make_int(Reason::Literal(pat.node())),
            );
        }
        PatKind::Float(_) => {
            constrain(
                ctx,
                &ty_pat,
                &TypeVar::make_float(Reason::Literal(pat.node())),
            );
        }
        PatKind::Bool(_) => {
            constrain(
                ctx,
                &ty_pat,
                &TypeVar::make_bool(Reason::Literal(pat.node())),
            );
        }
        PatKind::Str(_) => {
            constrain(
                ctx,
                &ty_pat,
                &TypeVar::make_string(Reason::Literal(pat.node())),
            );
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
                    let (enum_ty, substitution) = TypeVar::make_nominal_with_substitution(
                        ctx,
                        Reason::Node(pat.node()),
                        Nominal::Enum(enum_def.clone()),
                        pat.node(),
                    );

                    let variant_def = &enum_def.variants[variant];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_void(Reason::VariantNoData(variant_def.node())),
                        Some(ty) => ty.to_typevar(ctx),
                    };
                    let variant_data_ty = variant_data_ty.subst(&substitution);
                    constrain(ctx, &ty_data, &variant_data_ty);

                    constrain(ctx, &ty_pat, &enum_ty);

                    if let Some(data) = data {
                        generate_constraints_pat(ctx, Mode::ana(ty_data), data)
                    };
                } else {
                    ty_pat.set_flag_missing_info();
                }
            } else {
                // must resolve tag here based on inferred type
                if let Some((enum_def, idx)) = infer_enum(&mode, &tag.v) {
                    ctx.resolution_map.insert(
                        tag.id,
                        Declaration::EnumVariant {
                            e: enum_def.clone(),
                            variant: idx,
                        },
                    );

                    let (def_type, substitution) = TypeVar::make_nominal_with_substitution(
                        ctx,
                        Reason::Node(pat.node()),
                        Nominal::Enum(enum_def.clone()),
                        pat.node(),
                    );

                    let variant_def = &enum_def.variants[idx];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_void(Reason::VariantNoData(variant_def.node())),
                        Some(ty) => ty.to_typevar(ctx),
                    };
                    let variant_data_ty = variant_data_ty.subst(&substitution);
                    constrain(ctx, &ty_data, &variant_data_ty);

                    constrain(ctx, &ty_pat, &def_type);

                    if let Some(data) = data {
                        generate_constraints_pat(ctx, Mode::ana(ty_data), data)
                    };
                } else {
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
                &ty_pat,
                &TypeVar::make_tuple(tys_elements, Reason::Node(pat.node())),
            );
            if let Mode::Ana {
                constraint_reason,
                expected,
            } = &mode
                && let Some(PotentialType::Tuple(_, elems)) = expected.single()
            {
                for (pat, expected) in pats.iter().zip(elems) {
                    generate_constraints_pat(
                        ctx,
                        Mode::Ana {
                            expected,
                            constraint_reason: constraint_reason.clone(),
                        },
                        pat,
                    )
                }
            } else {
                for pat in pats {
                    generate_constraints_pat(ctx, Mode::Syn, pat)
                }
            }
        }
    }
    let ty_pat = TypeVar::from_node(ctx, pat.node());
    handle_ana(ctx, mode, ty_pat);
}

fn handle_ana(ctx: &mut StaticsContext, mode: Mode, node_ty: TypeVar) {
    match mode {
        Mode::Syn => (),
        Mode::Ana {
            expected,
            constraint_reason,
        } => {
            if let Some(constraint_reason) = constraint_reason {
                constrain_because(ctx, &expected, &node_ty, constraint_reason)
            } else {
                constrain(ctx, &expected, &node_ty)
            }
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

impl SolvedType {
    // TODO: need to use the args of the iface constraint
    pub(crate) fn implements_iface(&self, ctx: &StaticsContext, iface: &Rc<InterfaceDef>) -> bool {
        if let SolvedType::Poly(poly_decl) = &self {
            let ifaces = poly_decl.interfaces(ctx);
            return ifaces.iter().any(|constraint| &constraint.iface == iface);
        }
        self.get_iface_impls(ctx, iface).is_some()
    }

    pub(crate) fn get_iface_impls(
        &self,
        ctx: &StaticsContext,
        iface: &Rc<InterfaceDef>,
    ) -> Option<Rc<InterfaceImpl>> {
        let impl_list = ctx.interface_impls.get(iface).cloned()?;
        impl_list
            .iter()
            .find(|&imp| self.fits_impl(ctx, imp))
            .cloned()
    }

    pub(crate) fn fits_impl(&self, ctx: &StaticsContext, imp: &Rc<InterfaceImpl>) -> bool {
        let Some(impl_ty) = imp.typ.to_solved_type(ctx) else { return false };
        self.fits_impl_ty(ctx, &impl_ty)
    }

    pub(crate) fn fits_impl_ty(&self, ctx: &StaticsContext, impl_ty: &SolvedType) -> bool {
        match (self, &impl_ty) {
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
                        .all(|(ty1, ty2)| ty1.fits_impl_ty(ctx, ty2))
            }
            (SolvedType::Function(args1, out1), SolvedType::Function(args2, out2)) => {
                args1.len() == args2.len()
                    && args1
                        .iter()
                        .zip(args2.iter())
                        .all(|(ty1, ty2)| ty1.fits_impl_ty(ctx, ty2))
                    && out1.fits_impl_ty(ctx, out2)
            }
            (SolvedType::Nominal(ident1, tys1), SolvedType::Nominal(ident2, tys2)) => {
                ident1 == ident2
                    && tys1.len() == tys2.len()
                    && tys1
                        .iter()
                        .zip(tys2.iter())
                        .all(|(ty1, ty2)| ty1.fits_impl_ty(ctx, ty2))
            }
            (_, SolvedType::Poly(poly_decl)) => {
                let ifaces = poly_decl.interfaces(ctx);
                ifaces
                    .iter()
                    .all(|constraint| self.implements_iface(ctx, &constraint.iface))
            }
            _ => false,
        }
    }
}

impl Display for TypeVar {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let types = self.0.clone_data().types;
        match types.len() {
            0 => write!(f, "_"),
            1 => write!(f, "{}", self.single().unwrap()),
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
        }?;
        let iface_constraints = self.0.clone_data().iface_constraints;
        if iface_constraints.is_empty() {
            return Ok(());
        }
        write!(f, " impl ")?;
        for (constraint, _) in iface_constraints.iter() {
            write!(f, "{}", constraint.iface.name.v)?;
            if !constraint.args.is_empty() {
                write!(f, "<")?;
                for (i, (output_type, _, val)) in constraint.args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}={}", output_type.name.v, val)?;
                }
                write!(f, ">")?;
            }
        }
        Ok(())
    }
}

impl Display for PotentialType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PotentialType::Poly(_, decl) => {
                match decl {
                    PolytypeDeclaration::Ordinary(polyty) => {
                        write!(f, "{}", polyty.name.id)?;
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
                    }
                    PolytypeDeclaration::Builtin(_, name) => write!(f, "{}", name)?,
                    PolytypeDeclaration::InterfaceSelf(_) => write!(f, "Self")?,
                }

                Ok(())
            }
            PotentialType::InterfaceOutput(_, output_type) => {
                write!(f, "{}", output_type.name.v)
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
                match polyty {
                    // TODO: this is duplicated right above. Maybe implement Dispaly for PolytypeDeclaration
                    PolytypeDeclaration::Ordinary(polyty) => {
                        // TODO: why is this here?
                        write!(f, "{}", polyty.name.id)?;
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
                    }
                    PolytypeDeclaration::Builtin(_, name) => write!(f, "{}", name)?,
                    PolytypeDeclaration::InterfaceSelf(_) => {
                        write!(f, "Self")?;
                    }
                }

                Ok(())
            }
            SolvedType::InterfaceOutput(output_type) => {
                write!(f, "{}", output_type.name.v)
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
