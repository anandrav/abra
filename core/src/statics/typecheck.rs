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
use std::collections::{BTreeSet, HashMap};
use std::fmt::{self, Display, Write};
use std::rc::Rc;

use super::{
    Declaration, EnumDef, Error, FuncDef, InterfaceDecl, Polytype, StaticsContext, StructDef,
};

pub(crate) fn solve_types(ctx: &mut StaticsContext, files: &Vec<Rc<FileAst>>) {
    for file in files {
        generate_constraints_file(file.clone(), ctx);
    }
    check_unifvars(ctx);
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct TypeVar(UnionFindNode<TypeVarData>);

#[derive(Debug, Clone, PartialEq)]
pub(crate) struct TypeVarData {
    pub(crate) types: HashMap<TypeKey, PotentialType>,
    pub(crate) locked: bool,
}

impl TypeVarData {
    fn new() -> Self {
        Self {
            types: HashMap::new(),
            locked: false,
        }
    }

    fn singleton_solved(potential_type: PotentialType) -> Self {
        let mut types = HashMap::new();
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum PotentialType {
    Poly(Reasons, Declaration), // type name, then list of Interfaces it must match
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
    Poly(Declaration),
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
    Node(NodeId), // the type of an expression or statement located at NodeId
    InstantiateUdtParam(NodeId, u8),
    InstantiatePoly(NodeId, Rc<Polytype>),
    FuncArg(NodeId, u8), // u8 represents the index of the argument
    FuncOut(NodeId),     // u8 represents how many arguments before this output
    ListElem(NodeId),
}

// TODO: Most likely none of these should contain Box<Reason>. That's unnecessarily complicated
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum Reason {
    // TODO: get rid of Reason::Node if possible, but no rush
    Node(NodeId), // the type of an expression or statement located at NodeId
    Annotation(NodeId),
    Literal(NodeId),
    Builtin(Builtin), // a builtin function or constant, which doesn't exist in the AST
    Effect(u16),
    BinopLeft(NodeId),
    BinopRight(NodeId),
    BinopOut(NodeId),
    IndexAccess,
    VariantNoData(NodeId), // the type of the data of a variant with no data, always Unit.
    WhileLoopBody(NodeId),
    IfWithoutElse(NodeId),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) enum ConstraintReason {
    None, // TODO: get rid of None if possible, but no rush

    BinaryOperandsMustMatch(NodeId),
    IfElseBodies,
    LetStmtAnnotation,
    LetSetLhsRhs,
    MatchScrutinyAndPattern,
    FuncCall(NodeId),
    // bool
    Condition,
    BinaryOperandBool(NodeId),
    // int
    IndexAccess,
}

type Substitution = HashMap<Declaration, TypeVar>;

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
                let Declaration::Polytype(polyty) = decl else {
                    panic!();
                };
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

    fn make_poly(reason: Reason, decl: Declaration) -> PotentialType {
        PotentialType::Poly(reasons_singleton(reason), decl)
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

    fn is_underdetermined(&self) -> bool {
        self.0.with_data(|d| d.types.is_empty())
    }

    fn is_conflicted(&self) -> bool {
        self.0.with_data(|d| d.types.len() > 1)
    }

    fn is_locked(&self) -> bool {
        self.0.with_data(|d| d.locked)
    }

    fn clone_types(&self) -> HashMap<TypeKey, PotentialType> {
        self.0.clone_data().types
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
        id: NodeId,
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
                    let Declaration::Polytype(polyty) = decl else {
                        panic!()
                    };
                    // println!("-- time to instantiate");
                    let prov = Prov::InstantiatePoly(id, polyty.clone());
                    let ret = TypeVar::fresh(ctx, prov.clone());
                    let mut extension: Vec<(Rc<InterfaceDecl>, NodeId)> = Vec::new();
                    for i in &polyty.iface_names {
                        if let Some(Declaration::InterfaceDef(iface)) =
                            ctx.resolution_map.get(&i.id)
                        {
                            extension.push((iface.clone(), id));
                        }
                    }
                    ctx.unifvars_constrained_to_interfaces
                        .entry(prov)
                        .or_default()
                        .extend(extension);
                    return ret; // instantiation occurs here
                } else {
                    // println!("-- did not instantiate...");
                    if let Declaration::Polytype(polyty) = decl {
                        // println!("because it resolves to this:");
                        // print_node(ctx, polyty.name.id);
                    }
                    ty // noop
                }
            }
            PotentialType::Nominal(provs, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, id))
                    .collect();
                PotentialType::Nominal(provs, ident, params)
            }
            PotentialType::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, id))
                    .collect();
                let out = out.instantiate(polyvar_scope.clone(), ctx, id);
                PotentialType::Function(provs, args, out)
            }
            PotentialType::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(polyvar_scope.clone(), ctx, id))
                    .collect();
                PotentialType::Tuple(provs, elems)
            }
        };
        let mut types = HashMap::new();
        types.insert(ty.key(), ty);
        let data_instantiated = TypeVarData {
            types,
            locked: data.locked,
        };
        let tvar = TypeVar(UnionFindNode::new(data_instantiated));
        ctx.unifvars.insert(Prov::Node(id), tvar.clone());
        tvar
    }

    pub(crate) fn get_first_a(self) -> Option<Declaration> {
        let data = self.0.clone_data();
        if data.types.len() == 1 {
            let ty = data.types.into_values().next().unwrap();

            match ty {
                PotentialType::Unit(_)
                | PotentialType::Int(_)
                | PotentialType::Float(_)
                | PotentialType::Bool(_)
                | PotentialType::String(_) => None,
                PotentialType::Poly(_, ref decl) => {
                    let Declaration::Polytype(polyty) = decl else {
                        panic!()
                    };
                    Some(decl.clone())
                }
                PotentialType::Nominal(_, _, params) => {
                    for param in &params {
                        if let Some(decl) = param.clone().get_first_a() {
                            return Some(decl);
                        }
                    }
                    None
                }
                PotentialType::Function(_, args, out) => {
                    for arg in &args {
                        if let Some(decl) = arg.clone().get_first_a() {
                            return Some(decl);
                        }
                    }
                    out.get_first_a()
                }
                PotentialType::Tuple(_, elems) => {
                    for elem in &elems {
                        if let Some(decl) = elem.clone().get_first_a() {
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

    // TODO! I am not convinced that Polyvars are properly resolved and/or substituted. Will need to deep dive
    // Creates a *new* Type with polymorphic variabels replaced by subtitutions
    pub(crate) fn subst(self, prov: Prov, substitution: &HashMap<Declaration, TypeVar>) -> TypeVar {
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
                        .map(|ty| ty.subst(prov.clone(), substitution))
                        .collect();
                    PotentialType::Nominal(provs, ident, params)
                }
                PotentialType::Function(provs, args, out) => {
                    let args = args
                        .into_iter()
                        .map(|ty| ty.subst(prov.clone(), substitution))
                        .collect();
                    let out = out.subst(prov, substitution);
                    PotentialType::Function(provs, args, out)
                }
                PotentialType::Tuple(provs, elems) => {
                    let elems = elems
                        .into_iter()
                        .map(|ty| ty.subst(prov.clone(), substitution))
                        .collect();
                    PotentialType::Tuple(provs, elems)
                }
            };
            let mut types = HashMap::new();
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

    pub(crate) fn make_poly(reason: Reason, decl: Declaration) -> TypeVar {
        Self::singleton_solved(PotentialType::make_poly(reason, decl))
    }

    pub(crate) fn make_nominal(reason: Reason, nominal: Nominal, params: Vec<TypeVar>) -> TypeVar {
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

fn tyvar_of_declaration(
    ctx: &mut StaticsContext,
    decl: &Declaration,
    id: NodeId,
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
            let mut substitution: Substitution = HashMap::new();
            for i in 0..nparams {
                params.push(TypeVar::fresh(ctx, Prov::InstantiateUdtParam(id, i as u8)));
                // TODO: don't do this silly downcast.
                // ty_args should just be a Vec<Identifier> most likely
                let TypeKind::Poly(polyty) = &*enum_def.ty_args[i].kind else {
                    panic!()
                };
                let decl @ Declaration::Polytype(_) =
                    ctx.resolution_map.get(&polyty.name.id).unwrap()
                else {
                    panic!()
                };
                substitution.insert(decl.clone(), params[i].clone());
            }
            Some(TypeVar::make_nominal(
                Reason::Node(id), // TODO: change to Reason::Declaration
                Nominal::Enum(enum_def.clone()),
                params,
            ))
        }
        Declaration::EnumVariant { enum_def, variant } => {
            // TODO: The code for making a substitution is duplicated in a lot of places and it looks gross
            // TODO: hold on how the hell is this "substitution" different from instantiation
            let nparams = enum_def.ty_args.len();
            let mut params = vec![];
            let mut substitution: Substitution = HashMap::new();
            for i in 0..nparams {
                params.push(TypeVar::fresh(ctx, Prov::InstantiateUdtParam(id, i as u8)));
                // TODO: don't do this silly downcast.
                // ty_args should just be a Vec<Identifier> most likely
                let TypeKind::Poly(polyty) = &*enum_def.ty_args[i].kind else {
                    panic!()
                };
                let decl @ Declaration::Polytype(_) =
                    ctx.resolution_map.get(&polyty.name.id).unwrap()
                else {
                    panic!()
                };
                substitution.insert(decl.clone(), params[i].clone());
            }
            let def_type =
                TypeVar::make_nominal(Reason::Node(id), Nominal::Enum(enum_def.clone()), params);

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
                                e.clone().subst(Prov::Node(id), &substitution)
                            })
                            .collect();
                        Some(TypeVar::make_func(args, def_type, Reason::Node(id)))
                    }
                    _ => {
                        let ty = ast_type_to_typevar(ctx, ty.clone());
                        Some(TypeVar::make_func(
                            vec![ty.clone().subst(Prov::Node(id), &substitution)],
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
            let mut substitution: Substitution = HashMap::new();
            for i in 0..nparams {
                params.push(TypeVar::fresh(ctx, Prov::InstantiateUdtParam(id, i as u8)));
                // TODO: don't do this silly downcast.
                // ty_args should just be a Vec<Identifier> most likely
                let TypeKind::Poly(polyty) = &*struct_def.ty_args[i].kind else {
                    panic!()
                };
                let decl @ Declaration::Polytype(_) =
                    ctx.resolution_map.get(&polyty.name.id).unwrap()
                else {
                    panic!()
                };
                substitution.insert(decl.clone(), params[i].clone());
            }
            let def_type = TypeVar::make_nominal(
                Reason::Node(id),
                Nominal::Struct(struct_def.clone()),
                params,
            );
            let fields = struct_def
                .fields
                .iter()
                .map(|f| {
                    let ty = ast_type_to_typevar(ctx, f.ty.clone());
                    ty.clone().subst(Prov::Node(id), &substitution)
                })
                .collect();
            Some(TypeVar::make_func(fields, def_type, Reason::Node(id)))
        }
        Declaration::ForeignType(ident) => Some(TypeVar::make_nominal(
            Reason::Node(id),
            Nominal::ForeignType(ident.clone()),
            vec![],
        )),
        Declaration::Array => {
            let mut params = vec![];
            params.push(TypeVar::fresh(ctx, Prov::InstantiateUdtParam(id, 0)));

            let def_type = TypeVar::make_nominal(Reason::Node(id), Nominal::Array, params);

            Some(TypeVar::make_func(vec![], def_type, Reason::Node(id)))
        }
        Declaration::Polytype(_) => None,
        Declaration::Builtin(builtin) => {
            let ty_signature = builtin.type_signature();
            Some(ty_signature)
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

pub(crate) fn ast_type_to_solved_type(
    ctx: &StaticsContext,
    ast_type: Rc<AstType>,
) -> Option<SolvedType> {
    match &*ast_type.kind {
        TypeKind::Poly(polyty) => {
            // TODO: gross
            let mut ifaces = vec![];
            for iface_name in &polyty.iface_names {
                let lookup = ctx.resolution_map.get(&iface_name.id);
                if let Some(Declaration::InterfaceDef(iface_def)) = lookup {
                    ifaces.push(iface_def.clone());
                }
            }

            Some(SolvedType::Poly(polyty.clone()))
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
        TypeKind::Poly(polyty) => {
            if let Some(decl @ Declaration::Polytype(polyty)) =
                ctx.resolution_map.get(&polyty.name.id)
            {
                let mut interfaces = vec![];
                for iface_name in &polyty.iface_names {
                    let lookup = ctx.resolution_map.get(&iface_name.id);
                    if let Some(Declaration::InterfaceDef(iface_def)) = lookup {
                        interfaces.push(iface_def.clone());
                    }
                }
                TypeVar::make_poly(Reason::Annotation(ast_type.id()), decl.clone())
            } else {
                TypeVar::empty()
            }
        }
        TypeKind::Identifier(_) => {
            let lookup = ctx.resolution_map.get(&ast_type.id);
            match lookup {
                Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.id()),
                    Nominal::Enum(enum_def.clone()),
                    vec![],
                ),
                Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.id()),
                    Nominal::Struct(struct_def.clone()),
                    vec![],
                ),
                Some(Declaration::Array) => {
                    TypeVar::make_nominal(Reason::Annotation(ast_type.id()), Nominal::Array, vec![])
                }
                Some(Declaration::ForeignType(ident)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.id()),
                    Nominal::ForeignType(ident.clone()),
                    vec![],
                ),
                _ => {
                    // since resolution failed, unconstrained type
                    TypeVar::empty()
                }
            }
        }
        TypeKind::Ap(ident, params) => {
            let lookup = ctx.resolution_map.get(&ident.id);
            match lookup {
                Some(Declaration::Enum(enum_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.id()),
                    Nominal::Enum(enum_def.clone()),
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                Some(Declaration::Struct(struct_def)) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.id()),
                    Nominal::Struct(struct_def.clone()),
                    params
                        .iter()
                        .map(|param| ast_type_to_typevar(ctx, param.clone()))
                        .collect(),
                ),
                Some(Declaration::Array) => TypeVar::make_nominal(
                    Reason::Annotation(ast_type.id()),
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
        TypeKind::Unit => TypeVar::make_unit(Reason::Annotation(ast_type.id())),
        TypeKind::Int => TypeVar::make_int(Reason::Annotation(ast_type.id())),
        TypeKind::Float => TypeVar::make_float(Reason::Annotation(ast_type.id())),
        TypeKind::Bool => TypeVar::make_bool(Reason::Annotation(ast_type.id())),
        TypeKind::Str => TypeVar::make_string(Reason::Annotation(ast_type.id())),
        TypeKind::Function(lhs, rhs) => TypeVar::make_func(
            lhs.iter()
                .map(|t| ast_type_to_typevar(ctx, t.clone()))
                .collect(),
            ast_type_to_typevar(ctx, rhs.clone()),
            Reason::Annotation(ast_type.id()),
        ),
        TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_typevar(ctx, t.clone()));
            }
            TypeVar::make_tuple(statics_types, Reason::Annotation(ast_type.id()))
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
            constrain_solved_typevars(ctx, tyvar1, tyvar2, constraint_reason);
        }
        // Since exactly one of the TypeVars is unsolved, its data will be updated with information from the solved TypeVar
        (false, true) => {
            let potential_ty = tyvar2.0.clone_data().types.into_iter().next().unwrap().1;
            tyvar1.0.with_data(|d| {
                if d.types.is_empty() {
                    d.locked = true
                }
                d.extend(potential_ty)
            });
        }
        (true, false) => {
            let potential_ty = tyvar1.0.clone_data().types.into_iter().next().unwrap().1;
            tyvar2.0.with_data(|d| {
                if d.types.is_empty() {
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
    node_id: NodeId,
    iface: &Rc<InterfaceDecl>,
) {
    if let Some(ty) = tyvar.solution() {
        if !ty_implements_iface(ctx, ty.clone(), iface) {
            ctx.errors.push(Error::InterfaceNotImplemented {
                ty: ty.clone(),
                iface: iface.clone(),
                node_id,
            });
        }
    } else {
        let ifaces = ctx
            .unifvars_constrained_to_interfaces
            .entry(Prov::Node(node_id))
            .or_default();
        ifaces.push((iface.clone(), node_id));
    }
}

fn constrain_solved_typevars(
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

        // TODO! I am not convinced that Polyvars are properly resolved and/or substituted. Will need to deep dive
        // TODO! This is a temporary workaround to a problem with polyvar substitution/constraints/resolution
        // Removing this should not make things fail yet it does
        // TypeVar::merge(tyvar1, tyvar2);
    }
}

// TODO: Can this be done in resolve() instead?
#[derive(Clone)]
pub(crate) struct PolyvarScope {
    polyvars_in_scope: Environment<Declaration, ()>,
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

    fn lookup_poly(&self, decl: &Declaration) -> bool {
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
                    .push(Error::UnconstrainedUnifvar { node_id: *id });
            }
        }
    }
    // TODO: cloning sucks here
    for (prov, ifaces) in ctx.unifvars_constrained_to_interfaces.clone() {
        let ty = ctx.unifvars.get(&prov).unwrap().clone();
        if let Some(ty) = ty.solution() {
            for (iface, node_id) in ifaces.iter().cloned() {
                if !ty_implements_iface(ctx, ty.clone(), &iface) {
                    ctx.errors.push(Error::InterfaceNotImplemented {
                        ty: ty.clone(),
                        iface,
                        node_id,
                    });
                }
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
            if let Some(Declaration::InterfaceDef(iface_decl)) = &lookup {
                for method in &iface_decl.methods {
                    let node_ty = TypeVar::from_node(ctx, method.id());
                    if node_ty.is_locked() {
                        // Interface declaration method types have already been computed.
                        break;
                    }
                    let ty_annot = ast_type_to_typevar(ctx, method.ty.clone());
                    // TODO: Instead of creating an empty TypeVar (node_ty) and then immediately constraining it to a
                    // typevar created from a type annotation (ast_type_to_typevar(ty_annot)), do both in a single atomic step
                    constrain(ctx, node_ty.clone(), ty_annot.clone());
                }
                for f in &iface_impl.methods {
                    let method_name = f.name.v.clone();
                    if let Some(interface_method) =
                        iface_decl.methods.iter().find(|m| m.name.v == method_name)
                    {
                        let interface_method_ty =
                            ast_type_to_typevar(ctx, interface_method.ty.clone());
                        let actual = TypeVar::from_node(ctx, interface_method.id());
                        constrain(ctx, interface_method_ty.clone(), actual);

                        let mut substitution: Substitution = HashMap::new();
                        if let Some(ref decl @ Declaration::Polytype(ref polytype)) =
                            interface_method_ty.clone().get_first_a()
                        {
                            // print_node(ctx, polytype.name.id);
                            // println!("impl_ty: {}", impl_ty);
                            substitution.insert(decl.clone(), impl_ty.clone());
                        }

                        let expected = interface_method_ty
                            .clone()
                            .subst(Prov::Node(stmt.id), &substitution);

                        // println!("expected: {}", expected);

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
                // polyvar_scope.add_polys(&ty_ann, ctx);
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
            let ty_lhs = TypeVar::from_node(ctx, lhs.id);
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, lhs.clone(), ctx);
            let ty_rhs = TypeVar::from_node(ctx, rhs.id);
            generate_constraints_expr(polyvar_scope, Mode::Syn, rhs.clone(), ctx);
            constrain_because(ctx, ty_lhs, ty_rhs, ConstraintReason::LetSetLhsRhs);
        }
        StmtKind::FuncDef(f) => {
            generate_constraints_fn_def(ctx, polyvar_scope, f, f.name.id);
        }
        StmtKind::Break | StmtKind::Continue => {
            let enclosing_loop = ctx.loop_stack.last();
            match enclosing_loop {
                None | Some(None) => {
                    ctx.errors.push(Error::NotInLoop { node_id: stmt.id });
                }
                Some(Some(_node_id)) => {}
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
    let node_ty = TypeVar::from_node(ctx, expr.id);
    match &*expr.kind {
        ExprKind::Unit => {
            constrain(ctx, node_ty, TypeVar::make_unit(Reason::Literal(expr.id)));
        }
        ExprKind::Int(_) => {
            constrain(ctx, node_ty, TypeVar::make_int(Reason::Literal(expr.id)));
        }
        ExprKind::Float(_) => {
            constrain(ctx, node_ty, TypeVar::make_float(Reason::Literal(expr.id)));
        }
        ExprKind::Bool(_) => {
            constrain(ctx, node_ty, TypeVar::make_bool(Reason::Literal(expr.id)));
        }
        ExprKind::Str(s) => {
            constrain(ctx, node_ty, TypeVar::make_string(Reason::Literal(expr.id)));
            let len = ctx.string_constants.len();
            ctx.string_constants.entry(s.clone()).or_insert(len);
        }
        ExprKind::List(exprs) => {
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(expr.id));

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
                // TODO: log error? Or panic?
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
            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(expr.id));
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
                if let Some(typ) = tyvar_of_declaration(ctx, &res, expr.id) {
                    // print_node(ctx, expr.id);
                    // println!("ty before instantiate: {}", typ.clone());
                    let typ = typ.instantiate(polyvar_scope, ctx, expr.id);
                    // println!("ty after instantiate: {}", typ.clone());
                    constrain(ctx, typ, node_ty.clone());
                }
            }
        }
        ExprKind::BinOp(left, op, right) => {
            // print_node(ctx, expr.id);

            let ty_left = TypeVar::from_node(ctx, left.id);
            let ty_right = TypeVar::from_node(ctx, right.id);
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, left.clone(), ctx);
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, right.clone(), ctx);
            let ty_out = node_ty;

            let num_iface_decl = ctx
                .global_namespace
                .namespaces
                .get("prelude")
                .and_then(|p| p.declarations.get("Num"))
                .unwrap()
                .clone();
            let Declaration::InterfaceDef(num_iface_def) = num_iface_decl else {
                panic!()
            };

            let equal_iface_decl = ctx
                .global_namespace
                .namespaces
                .get("prelude")
                .and_then(|p| p.declarations.get("Equal"))
                .unwrap()
                .clone();
            let Declaration::InterfaceDef(equal_iface_def) = equal_iface_decl else {
                panic!()
            };

            let tostring_iface_decl = ctx
                .global_namespace
                .namespaces
                .get("prelude")
                .and_then(|p| p.declarations.get("ToString"))
                .unwrap()
                .clone();
            let Declaration::InterfaceDef(tostring_iface_def) = tostring_iface_decl else {
                panic!()
            };

            let reason_left = Reason::BinopLeft(expr.id);
            let reason_right = Reason::BinopRight(expr.id);
            let reason_out = Reason::BinopOut(expr.id);
            match op {
                BinaryOperator::And | BinaryOperator::Or => {
                    constrain_because(
                        ctx,
                        ty_left,
                        TypeVar::make_bool(reason_left),
                        ConstraintReason::BinaryOperandBool(expr.id),
                    );
                    constrain_because(
                        ctx,
                        ty_right,
                        TypeVar::make_bool(reason_right),
                        ConstraintReason::BinaryOperandBool(expr.id),
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
                        ConstraintReason::BinaryOperandsMustMatch(expr.id),
                    );
                    constrain_to_iface(ctx, ty_left.clone(), left.id, &num_iface_def);
                    constrain_to_iface(ctx, ty_right, right.id, &num_iface_def);
                    constrain(ctx, ty_left, ty_out);
                }
                BinaryOperator::Mod => {
                    constrain_because(
                        ctx,
                        ty_left,
                        TypeVar::make_int(reason_left),
                        ConstraintReason::BinaryOperandsMustMatch(expr.id),
                    );
                    constrain_because(
                        ctx,
                        ty_right,
                        TypeVar::make_int(reason_right),
                        ConstraintReason::BinaryOperandsMustMatch(expr.id),
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
                        ConstraintReason::BinaryOperandsMustMatch(expr.id),
                    );
                    constrain_to_iface(ctx, ty_left, left.id, &num_iface_def);
                    constrain_to_iface(ctx, ty_right, right.id, &num_iface_def);
                    constrain(ctx, ty_out, TypeVar::make_bool(reason_out));
                }
                BinaryOperator::Format => {
                    constrain_to_iface(ctx, ty_left.clone(), left.id, &tostring_iface_def);
                    constrain_to_iface(ctx, ty_right.clone(), right.id, &tostring_iface_def);
                    constrain_because(
                        ctx,
                        ty_out,
                        TypeVar::make_string(reason_out),
                        ConstraintReason::BinaryOperandsMustMatch(expr.id),
                    );
                }
                BinaryOperator::Equal => {
                    constrain_because(
                        ctx,
                        ty_left.clone(),
                        ty_right.clone(),
                        ConstraintReason::BinaryOperandsMustMatch(expr.id),
                    );
                    constrain_to_iface(ctx, ty_left.clone(), left.id, &equal_iface_def);
                    constrain_to_iface(ctx, ty_right.clone(), right.id, &equal_iface_def);
                    constrain(ctx, ty_out, TypeVar::make_bool(reason_out));
                }
            }
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
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.id)),
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
                            expected: TypeVar::make_unit(Reason::IfWithoutElse(expr.id)),
                        },
                        expr1.clone(),
                        ctx,
                    );
                    constrain(
                        ctx,
                        node_ty,
                        TypeVar::make_unit(Reason::IfWithoutElse(expr.id)),
                    )
                }
            }
        }
        ExprKind::WhileLoop(cond, expr) => {
            generate_constraints_expr(
                polyvar_scope.clone(),
                Mode::AnaWithReason {
                    expected: TypeVar::make_bool(Reason::Node(cond.id)),
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
                TypeVar::make_unit(Reason::WhileLoopBody(expr.id)),
            )
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
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, func.clone(), ctx);
            let ty_func = TypeVar::from_node(ctx, func.id);

            // arguments
            let tys_args: Vec<TypeVar> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = TypeVar::fresh(ctx, Prov::FuncArg(func.id, n as u8));
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
            let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(func.id));
            constrain(ctx, ty_body.clone(), node_ty);

            // function type
            let ty_args_and_body = TypeVar::make_func(tys_args, ty_body, Reason::Node(expr.id));

            if let ExprKind::Identifier(_ident) = &*func.kind {
                // println!("{_ident}()");
            }
            constrain_because(
                ctx,
                ty_args_and_body.clone(),
                ty_func.clone(),
                ConstraintReason::FuncCall(expr.id),
            );
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
            let ty_expr = TypeVar::from_node(ctx, expr.id);
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
                let mut resolved = false;
                for field in &struct_def.fields {
                    if field.name.v == *field_ident {
                        let ty_field = ast_type_to_typevar(ctx, field.ty.clone());
                        constrain(ctx, node_ty.clone(), ty_field);
                        resolved = true;
                    }
                }
                if !resolved {
                    ctx.errors
                        .push(Error::UnresolvedIdentifier { node_id: field.id })
                }
            }
        }
        ExprKind::IndexAccess(accessed, index) => {
            generate_constraints_expr(polyvar_scope.clone(), Mode::Syn, accessed.clone(), ctx);

            let elem_ty = TypeVar::fresh(ctx, Prov::ListElem(accessed.id));
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
    let node_ty = TypeVar::from_node(ctx, expr.id);
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
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node_id));
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
    let ty_body = TypeVar::fresh(ctx, Prov::FuncOut(node_id));

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

    constrain(ctx, ty_fun_name, ty_func.clone());
}

fn generate_constraints_pat(
    polyvar_scope: PolyvarScope,
    mode: Mode,
    pat: Rc<Pat>,
    ctx: &mut StaticsContext,
) {
    let ty_pat = TypeVar::from_node(ctx, pat.id);
    match &*pat.kind {
        PatKind::Wildcard => (),
        PatKind::Unit => {
            constrain(ctx, ty_pat, TypeVar::make_unit(Reason::Literal(pat.id)));
        }
        PatKind::Int(_) => {
            constrain(ctx, ty_pat, TypeVar::make_int(Reason::Literal(pat.id)));
        }
        PatKind::Float(_) => {
            constrain(ctx, ty_pat, TypeVar::make_float(Reason::Literal(pat.id)));
        }
        PatKind::Bool(_) => {
            constrain(ctx, ty_pat, TypeVar::make_bool(Reason::Literal(pat.id)));
        }
        PatKind::Str(_) => {
            constrain(ctx, ty_pat, TypeVar::make_string(Reason::Literal(pat.id)));
        }
        PatKind::Binding(_) => {}
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => TypeVar::from_node(ctx, data.id),
                None => TypeVar::make_unit(Reason::VariantNoData(pat.id)),
            };
            let mut substitution: Substitution = HashMap::new();
            let ty_enum_instance = {
                if let Some(Declaration::EnumVariant { enum_def, variant }) =
                    ctx.resolution_map.get(&tag.id).cloned()
                {
                    let nparams = enum_def.ty_args.len();
                    let mut params = vec![];
                    for i in 0..nparams {
                        params.push(TypeVar::fresh(
                            ctx,
                            Prov::InstantiateUdtParam(pat.id, i as u8),
                        ));
                        // TODO: don't do this silly downcast.
                        // ty_args should just be a Vec<Identifier> most likely
                        let TypeKind::Poly(polyty) = &*enum_def.ty_args[i].kind else {
                            panic!()
                        };
                        let decl @ Declaration::Polytype(_) =
                            ctx.resolution_map.get(&polyty.name.id).unwrap()
                        else {
                            panic!()
                        };
                        substitution.insert(decl.clone(), params[i].clone());
                    }
                    let def_type = TypeVar::make_nominal(
                        Reason::Node(pat.id),
                        Nominal::Enum(enum_def.clone()),
                        params,
                    );

                    let variant_def = &enum_def.variants[variant as usize];
                    let variant_data_ty = match &variant_def.data {
                        None => TypeVar::make_unit(Reason::VariantNoData(variant_def.id)),
                        Some(ty) => ast_type_to_typevar(ctx, ty.clone()),
                    };
                    let variant_data_ty = variant_data_ty.subst(Prov::Node(pat.id), &substitution);
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
    let ty_pat = TypeVar::from_node(ctx, pat.id);
    match mode {
        Mode::Syn => (),
        Mode::AnaWithReason {
            expected,
            constraint_reason,
        } => constrain_because(ctx, expected, ty_pat.clone(), constraint_reason),
        Mode::Ana { expected } => constrain(ctx, expected, ty_pat.clone()),
    };
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

// pub(crate) fn solved_type_to_typevar(ty: SolvedType, reason: Reason) -> TypeVar {
//     match ty {
//         SolvedType::Unit => TypeVar::make_unit(reason),
//         SolvedType::Int => TypeVar::make_int(reason),
//         SolvedType::Float => TypeVar::make_float(reason),
//         SolvedType::Bool => TypeVar::make_bool(reason),
//         SolvedType::String => TypeVar::make_string(reason),
//         SolvedType::Tuple(elements) => {
//             let elements = elements
//                 .into_iter()
//                 .map(|e| solved_type_to_typevar(e, reason.clone()))
//                 .collect();
//             TypeVar::make_tuple(elements, reason)
//         }
//         SolvedType::Function(args, out) => {
//             let args = args
//                 .into_iter()
//                 .map(|a| solved_type_to_typevar(a, reason.clone()))
//                 .collect();
//             let out = solved_type_to_typevar(*out, reason.clone());
//             TypeVar::make_func(args, out, reason.clone())
//         }
//         SolvedType::Nominal(name, params) => {
//             let params = params
//                 .into_iter()
//                 .map(|p| solved_type_to_typevar(p, reason.clone()))
//                 .collect();
//             TypeVar::make_nominal(reason, name, params)
//         }
//         SolvedType::Poly(polyty) => {
//             TypeVar::make_poly(reason, Declaration::Polytype(polyty.clone()))
//         }
//     }
// }

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
    ctx: &mut StaticsContext,
    ty: SolvedType,
    iface: &Rc<InterfaceDecl>,
) -> bool {
    if let SolvedType::Poly(polyty) = &ty {
        let mut ifaces = vec![];
        for iface_name in &polyty.iface_names {
            if let Some(Declaration::InterfaceDef(iface)) = ctx.resolution_map.get(&iface_name.id) {
                ifaces.push(iface.clone());
            }
        }
        if ifaces.contains(iface) {
            return true;
        }
    }
    let impl_list = ctx.interface_impls.entry(iface.clone()).or_default();
    let mut found = false;
    // TODO: cloning here sucks
    for imp in impl_list.clone() {
        let impl_ty = ast_type_to_typevar(ctx, imp.typ.clone());
        if let Some(impl_ty) = impl_ty.solution() {
            if ty_fits_impl_ty(ctx, ty.clone(), impl_ty).is_ok() {
                found = true;
            }
        }
    }
    found
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
        (SolvedType::Nominal(ident1, tys1), SolvedType::Nominal(ident2, tys2)) => {
            if ident1 == ident2 && tys1.len() == tys2.len() {
                for (ty1, ty2) in tys1.iter().zip(tys2.iter()) {
                    let SolvedType::Poly(polyty) = ty2.clone() else {
                        panic!()
                    };
                    // TODO: gross
                    let mut ifaces = BTreeSet::new();
                    for iface_name in &polyty.iface_names {
                        if let Some(Declaration::InterfaceDef(iface)) =
                            ctx.resolution_map.get(&iface_name.id)
                        {
                            ifaces.insert(iface.clone());
                        }
                    }
                    if !ty_fits_impl_ty_poly(ctx, ty1.clone(), ifaces) {
                        return Err((typ, impl_ty));
                    }
                }
                Ok(())
            } else {
                Err((typ, impl_ty))
            }
        }
        (_, SolvedType::Poly(polyty)) => {
            // TODO: code duplication with Nominal case above^
            // TODO: gross
            let mut ifaces = BTreeSet::new();
            for iface_name in &polyty.iface_names {
                if let Some(Declaration::InterfaceDef(iface)) =
                    ctx.resolution_map.get(&iface_name.id)
                {
                    ifaces.insert(iface.clone());
                }
            }
            if !ty_fits_impl_ty_poly(ctx, typ.clone(), ifaces) {
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
    interfaces: BTreeSet<Rc<InterfaceDecl>>,
) -> bool {
    for interface in interfaces {
        if let SolvedType::Poly(polyty) = &typ {
            // TODO: WTF does the next line mean:
            // if 'a Interface1 is constrained to [Interfaces...], ignore

            // TODO: gross
            let mut ifaces = Vec::new();
            for iface_name in &polyty.iface_names {
                if let Some(Declaration::InterfaceDef(iface)) =
                    ctx.resolution_map.get(&iface_name.id)
                {
                    ifaces.push(iface.clone());
                }
            }
            if ifaces.contains(&interface) {
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
            PotentialType::Poly(_, decl) => {
                let Declaration::Polytype(polyty) = decl else {
                    panic!()
                };
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

use codespan_reporting::diagnostic::{Diagnostic, Label};
use codespan_reporting::files::SimpleFiles;
use codespan_reporting::term;
use codespan_reporting::term::termcolor::{ColorChoice, StandardStream};
fn _print_node(ctx: &StaticsContext, node_id: NodeId) {
    let mut files = SimpleFiles::new();
    let mut filename_to_id = HashMap::<String, usize>::new();
    for (filename, source) in ctx._sources.filename_to_source.iter() {
        let id = files.add(filename, source);
        filename_to_id.insert(filename.clone(), id);
    }

    let get_file_and_range = |id: &NodeId| {
        let span = ctx._node_map.get(id).unwrap().span();
        (filename_to_id[&span.filename], span.range())
    };

    let (file, range) = get_file_and_range(&node_id);

    let diagnostic = Diagnostic::note().with_labels(vec![Label::secondary(file, range)]);

    let writer = StandardStream::stderr(ColorChoice::Always);
    let config = codespan_reporting::term::Config::default();

    term::emit(&mut writer.lock(), &config, &files, &diagnostic).unwrap();
}
