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
    // a type which must be solved for
    UnifVar(UnifVar),

    // "type must be equal to this"
    Poly(Provs, Identifier),
    Unit(Provs),
    Int(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<Type>, Box<Type>),
    Tuple(Provs, Vec<Type>),
    DefInstance(Provs, Identifier, Vec<Type>),
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

type UnifVar = UnionFindNode<UnifVarData>;

#[derive(Debug, Clone, PartialEq)]
pub struct UnifVarData {
    pub types: BTreeMap<TypeKey, Type>,
}

impl UnifVarData {
    pub fn solution(&self) -> Option<Type> {
        if self.types.len() == 1 {
            Some(self.types.values().next().unwrap().clone())
        } else {
            None
        }
    }
}

// If two types don't share the same key, they must be in conflict
// If two types share the same key, they may be in conflict
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeKey {
    Poly,                  // TODO: why isn't the Identifier included here?
    TyApp(Identifier, u8), // u8 represents the number of type params
    Unit,
    Int,
    Bool,
    String,
    Arrow(u8), // u8 represents the number of arguments
    Tuple(u8), // u8 represents the number of elements
}

// Provenances are used to:
// (1) track the origins (plural!) of a type solution
// (2) give the *unique* identity of an unknown type variable (UnifVar) in the SolutionMap
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Prov {
    Node(ast::Id),   // the type of an expression or statement
    Builtin(String), // a builtin function or constant, which doesn't exist in the AST

    Alias(Identifier),
    AdtDef(Box<Prov>),

    InstantiateAdtParam(Box<Prov>, u8),
    InstantiatePoly(Box<Prov>, Identifier),
    FuncArg(Box<Prov>, u8),   // u8 represents the index of the argument
    FuncOut(Box<Prov>),       // u8 represents how many arguments before this output
    VariantNoData(Box<Prov>), // the type of the data of a variant with no data, always Unit.
}

impl Type {
    pub fn key(&self) -> Option<TypeKey> {
        match self {
            Type::UnifVar(_) => None,
            Type::Poly(_, _) => Some(TypeKey::Poly),
            Type::Unit(_) => Some(TypeKey::Unit),
            Type::Int(_) => Some(TypeKey::Int),
            Type::Bool(_) => Some(TypeKey::Bool),
            Type::String(_) => Some(TypeKey::String),
            Type::Function(_, args, _) => Some(TypeKey::Arrow(args.len() as u8)),
            Type::Tuple(_, elems) => Some(TypeKey::Tuple(elems.len() as u8)),
            Type::DefInstance(_, ident, params) => {
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
            Type::Unit(_) | Type::Int(_) | Type::Bool(_) | Type::String(_) => {
                println!("it was a noop");
                self // noop
            }
            Type::UnifVar(unifvar) => {
                let data = unifvar.clone_data();
                // TODO consider relaxing the types.len() == 1 if it gives better editor feedback. But test thoroughly after
                if data.types.len() == 1 {
                    let ty = data.types.into_values().next().unwrap();
                    if let Type::Poly(_, _) = ty {
                        // println!("it was a unifvar with a poly var in it");
                        ty.instantiate(gamma, inf_ctx, prov)
                    } else {
                        // println!("it was a unifvar but no polyvar.");
                        let ty = ty.instantiate(gamma, inf_ctx, prov.clone());
                        let mut types = BTreeMap::new();
                        types.insert(ty.key().unwrap(), ty);
                        let data_instantiated = UnifVarData { types };
                        // unifvar.replace_data(data_instantiated);
                        // // unifvar.with_data(|data| *data = data_instantiated);
                        // Type::UnifVar(unifvar)

                        let unifvar = UnionFindNode::new(data_instantiated);
                        inf_ctx.vars.insert(prov, unifvar.clone());
                        Type::UnifVar(unifvar) // TODO clone this? But test thoroughly after lol
                    }
                } else {
                    // println!("it was a unifvar but a noop");
                    Type::UnifVar(unifvar) // noop
                }
            }
            Type::Poly(_, ref ident) => {
                // println!("it was a INSTANTIATE POLY, ident: {:?}", ident);
                if !gamma.borrow().lookup_poly(ident) {
                    Type::fresh_unifvar(
                        inf_ctx,
                        Prov::InstantiatePoly(Box::new(prov), ident.clone()),
                    )
                } else {
                    self // noop
                }
            }
            Type::DefInstance(provs, ident, params) => {
                // println!("it was a def instance");
                let params = params
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                Type::DefInstance(provs, ident, params)
            }
            Type::Function(provs, args, out) => {
                println!("it was a func");
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(gamma.clone(), inf_ctx, prov.clone()))
                    .collect();
                let out = Box::new(out.instantiate(gamma, inf_ctx, prov));
                Type::Function(provs, args, out)
            }
            Type::Tuple(provs, elems) => {
                println!("it was a tuple");
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
            Type::Unit(_) | Type::Int(_) | Type::Bool(_) | Type::String(_) => {
                println!("it was a noop");
                self // noop
            }
            Type::UnifVar(unifvar) => {
                let data = unifvar.clone_data();
                // TODO consider relaxing the types.len() == 1 if it gives better editor feedback. But test thoroughly after
                // if data.types.len() == 1 {
                let ty = data.types.into_values().next().unwrap();
                if let Type::Poly(_, _) = ty {
                    ty.subst(gamma, inf_ctx, prov, substitution)
                } else {
                    let ty = ty.subst(gamma, inf_ctx, prov.clone(), substitution);
                    let mut types = BTreeMap::new();
                    types.insert(ty.key().unwrap(), ty);
                    let data_instantiated = UnifVarData { types };

                    let unifvar = UnionFindNode::new(data_instantiated);
                    inf_ctx.vars.insert(prov, unifvar.clone());
                    Type::UnifVar(unifvar) // TODO clone this? But test thoroughly after lol
                }
                // } else {
                //     Type::UnifVar(unifvar) // noop
                // }
            }
            Type::Poly(_, ref ident) => {
                if !gamma.borrow().lookup_poly(ident) {
                    if let Some(ty) = substitution.get(ident) {
                        ty.clone()
                    } else {
                        self // noop
                    }
                } else {
                    self // noop
                }
            }
            Type::DefInstance(provs, ident, params) => {
                let params = params
                    .into_iter()
                    .map(|ty| ty.subst(gamma.clone(), inf_ctx, prov.clone(), substitution))
                    .collect();
                Type::DefInstance(provs, ident, params)
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

    pub fn make_poly(prov: Prov, ident: String) -> Type {
        Type::Poly(provs_singleton(prov), ident)
    }

    pub fn make_def_instance(prov: Prov, ident: String, params: Vec<Type>) -> Type {
        Type::DefInstance(provs_singleton(prov), ident, params)
    }

    pub fn make_unit(prov: Prov) -> Type {
        Type::Unit(provs_singleton(prov))
    }

    pub fn make_int(prov: Prov) -> Type {
        Type::Int(provs_singleton(prov))
    }

    pub fn make_bool(prov: Prov) -> Type {
        Type::Bool(provs_singleton(prov))
    }

    pub fn make_string(prov: Prov) -> Type {
        Type::String(provs_singleton(prov))
    }

    pub fn make_arrow(args: Vec<Type>, out: Type, id: ast::Id) -> Type {
        Type::Function(provs_singleton(Prov::Node(id)), args, out.into())
    }

    pub fn make_tuple(elems: Vec<Type>, id: ast::Id) -> Type {
        Type::Tuple(provs_singleton(Prov::Node(id)), elems)
    }

    pub fn provs(&self) -> &Provs {
        match self {
            Self::UnifVar(_) => panic!("Type::provs called on Type::Var"),
            Self::Poly(provs, _)
            | Self::Unit(provs)
            | Self::Int(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _)
            | Self::DefInstance(provs, _, _) => provs,
        }
    }
}

pub fn types_of_binop(opcode: &BinOpcode, id: ast::Id) -> (Type, Type, Type) {
    match opcode {
        BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => (
            Type::make_int(Prov::Node(id)),
            Type::make_int(Prov::Node(id)),
            Type::make_int(Prov::Node(id)),
        ),
        BinOpcode::Equals
        | BinOpcode::LessThan
        | BinOpcode::GreaterThan
        | BinOpcode::LessThanOrEqual
        | BinOpcode::GreaterThanOrEqual => (
            Type::make_int(Prov::Node(id)),
            Type::make_int(Prov::Node(id)),
            Type::make_bool(Prov::Node(id)),
        ),
    }
}

pub fn ast_type_to_statics_type(
    inf_ctx: &mut InferenceContext,
    ast_type: Rc<ast::AstType>,
) -> Type {
    match &*ast_type.typekind {
        ast::TypeKind::Poly(ident) => Type::make_poly(Prov::Node(ast_type.id()), ident.clone()),
        ast::TypeKind::Alias(ident) => Type::fresh_unifvar(inf_ctx, Prov::Alias(ident.clone())),
        ast::TypeKind::Ap(ident, params) => Type::DefInstance(
            provs_singleton(Prov::Node(ast_type.id())),
            ident.clone(),
            params
                .iter()
                .map(|param| ast_type_to_statics_type(inf_ctx, param.clone()))
                .collect(),
        ),
        ast::TypeKind::Unit => Type::make_unit(Prov::Node(ast_type.id())),
        ast::TypeKind::Int => Type::make_int(Prov::Node(ast_type.id())),
        ast::TypeKind::Bool => Type::make_bool(Prov::Node(ast_type.id())),
        ast::TypeKind::Str => Type::make_string(Prov::Node(ast_type.id())),
        // TODO wait does this only allow one argument??
        ast::TypeKind::Arrow(lhs, rhs) => Type::make_arrow(
            vec![ast_type_to_statics_type(inf_ctx, lhs.clone())],
            ast_type_to_statics_type(inf_ctx, rhs.clone()),
            ast_type.id(),
        ),
        ast::TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_statics_type(inf_ctx, t.clone()));
            }
            Type::make_tuple(statics_types, ast_type.id())
        }
    }
}

pub type Provs = RefCell<BTreeSet<Prov>>;

pub fn provs_singleton(prov: Prov) -> Provs {
    let mut set = BTreeSet::new();
    set.insert(prov);
    RefCell::new(set)
}

pub struct InferenceContext {
    // unification variables which must be solved
    pub vars: HashMap<Prov, UnifVar>,
    // nominal type definitions (ADTs)
    pub tydefs: HashMap<Identifier, AdtDef>,
    // map from variant names to ADT names
    pub variants_to_adt: HashMap<Identifier, Identifier>,
}

impl InferenceContext {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
            tydefs: HashMap::new(),
            variants_to_adt: HashMap::new(),
        }
    }

    pub fn adt_def_of_name(&self, name: &Identifier) -> Option<AdtDef> {
        self.tydefs.get(name).cloned()
    }

    pub fn adt_def_of_variant(&self, variant: &Identifier) -> Option<AdtDef> {
        let adt_name = self.variants_to_adt.get(variant)?;
        self.tydefs.get(adt_name).cloned()
    }
}

impl UnifVarData {
    fn empty() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    // TODO: occurs check
    fn extend(&mut self, t_other: Type) {
        let key = t_other.key().unwrap();

        // accumulate provenances and constrain children to each other if applicable
        if let Some(t) = self.types.get_mut(&key) {
            match &t_other {
                Type::UnifVar(_) => panic!("should not be Type::UnifVar"),
                Type::Poly(other_provs, _)
                | Type::Unit(other_provs)
                | Type::Int(other_provs)
                | Type::Bool(other_provs)
                | Type::String(other_provs) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                }
                Type::Function(other_provs, args1, out1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let Type::Function(_, args2, out2) = t {
                        if args1.len() == args2.len() {
                            // TODO unnecessary because key contains arity
                            for (arg, arg2) in args1.iter().zip(args2.iter()) {
                                constrain(arg.clone(), arg2.clone());
                            }
                            constrain(*out1.clone(), *out2.clone());
                        } else {
                            panic!("should be same length")
                        }
                    }
                }
                Type::Tuple(other_provs, elems1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let Type::Tuple(_, elems2) = t {
                        if elems1.len() == elems2.len() {
                            // TODO unnecessary because key contains arity
                            for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                                constrain(elem.clone(), elem2.clone());
                            }
                        } else {
                            panic!("should be same length")
                        }
                    }
                }
                Type::DefInstance(other_provs, _, other_tys) => {
                    if let Type::DefInstance(_, _, tys) = t {
                        if tys.len() == other_tys.len() {
                            for (ty, other_ty) in tys.iter().zip(other_tys.iter()) {
                                println!("{} CONSTRAIN TO {}", ty, other_ty);
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

    // TODO: occurs check
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

pub fn make_new_environment() -> Rc<RefCell<Gamma>> {
    let gamma = Gamma::empty();
    gamma.borrow_mut().extend(
        &String::from("print"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_string(Prov::FuncArg(
                Box::new(Prov::Builtin("print: string -> void".to_string())),
                0,
            ))],
            Type::make_unit(Prov::FuncOut(Box::new(Prov::Builtin(
                "print: string -> void".to_string(),
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
    gamma
}

impl fmt::Debug for Gamma {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:?}\n)", Gamma::debug_helper(self))
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
            Type::Poly(_, ident) => {
                self.poly_type_vars.insert(ident.clone());
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
        ExprKind::Bool(_) => {
            constrain(node_ty, Type::make_bool(Prov::Node(expr.id)));
        }
        ExprKind::Str(_) => {
            constrain(node_ty, Type::make_string(Prov::Node(expr.id)));
        }
        ExprKind::Var(id) => {
            let lookup = gamma.borrow_mut().lookup(id);
            if let Some(typ) = lookup {
                // replace polymorphic types with unifvars if necessary
                println!("instantiating type with id: {}", id);
                let typ = typ.instantiate(gamma, inf_ctx, Prov::Node(expr.id));
                println!("{}", typ);
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
                // let def_type =
                //     def_type.subst(gamma.clone(), inf_ctx, Prov::Node(expr.id), &substitution);
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
                    constrain(node_ty, Type::make_arrow(args, def_type, expr.id));
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
                            expr.id,
                        ),
                    );
                }
                return;
            }
            panic!("variable not bound in TyCtx: {}", id);
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op, expr.id);
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
                generate_constraints_stmt(new_gamma.clone(), Mode::Syn, statement.clone(), inf_ctx);
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
            let (ty_func, _body_gamma) = generate_constraints_function_helper(
                gamma, inf_ctx, args, out_annot, body, expr.id,
            );

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
            let ty_func = Type::make_arrow(tys_args, ty_body, expr.id);
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
            constrain(Type::make_tuple(tys, expr.id), node_ty);
            for expr in exprs {
                generate_constraints_expr(gamma.clone(), Mode::Syn, expr.clone(), inf_ctx);
            }
        }
    }
}

// helper function for common code between Expr::Func and Expr::LetFunc
pub fn generate_constraints_function_helper(
    gamma: Rc<RefCell<Gamma>>,
    inf_ctx: &mut InferenceContext,
    args: &[(Rc<ast::Pat>, Option<Rc<ast::AstType>>)],
    out_annot: &Option<Rc<ast::AstType>>,
    body: &Rc<Expr>,
    func_node_id: ast::Id,
) -> (Type, Rc<RefCell<Gamma>>) {
    // arguments
    let body_gamma = Gamma::new(Some(gamma));
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = Type::from_node(inf_ctx, arg.id);
            if let Some(arg_annot) = arg_annot {
                let arg_annot = ast_type_to_statics_type(inf_ctx, arg_annot.clone());
                body_gamma.borrow_mut().add_polys(&arg_annot);
                generate_constraints_pat(
                    body_gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                    Mode::Ana {
                        expected: arg_annot,
                    },
                    arg.clone(),
                    inf_ctx,
                )
            } else {
                generate_constraints_pat(body_gamma.clone(), Mode::Syn, arg.clone(), inf_ctx)
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = Type::fresh_unifvar(inf_ctx, Prov::FuncOut(Box::new(Prov::Node(func_node_id))));
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
            body_gamma.clone(),
            Mode::Ana {
                expected: out_annot,
            },
            body.clone(),
            inf_ctx,
        );
    }

    (Type::make_arrow(ty_args, ty_body, func_node_id), body_gamma)
}

pub fn generate_constraints_stmt(
    gamma: Rc<RefCell<Gamma>>,
    mode: Mode,
    stmt: Rc<Stmt>,
    inf_ctx: &mut InferenceContext,
) {
    match &*stmt.stmtkind {
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
        StmtKind::Let((pat, ty_ann), expr) => {
            let ty_pat = Type::from_node(inf_ctx, pat.id);

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_statics_type(inf_ctx, ty_ann.clone());
                gamma.borrow_mut().add_polys(&ty_ann);
                generate_constraints_pat(
                    gamma.clone(),
                    Mode::Ana { expected: ty_ann },
                    pat.clone(),
                    inf_ctx,
                )
            } else {
                generate_constraints_pat(gamma.clone(), Mode::Syn, pat.clone(), inf_ctx)
            };

            generate_constraints_expr(gamma, Mode::Ana { expected: ty_pat }, expr.clone(), inf_ctx);
        }
        StmtKind::LetFunc(name, args, out_annot, body) => {
            let func_node_id = stmt.id;

            let ty_pat = Type::from_node(inf_ctx, name.id);
            gamma
                .borrow_mut()
                .extend(&name.patkind.get_identifier_of_variable(), ty_pat.clone());

            let body_gamma = Gamma::new(Some(gamma));

            // BEGIN TODO use helper function for functions again

            // arguments
            let ty_args = args
                .iter()
                .map(|(arg, arg_annot)| {
                    let ty_pat = Type::from_node(inf_ctx, arg.id);
                    if let Some(arg_annot) = arg_annot {
                        let arg_annot = ast_type_to_statics_type(inf_ctx, arg_annot.clone());
                        body_gamma.borrow_mut().add_polys(&arg_annot);
                        generate_constraints_pat(
                            body_gamma.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                            Mode::Ana {
                                expected: arg_annot,
                            },
                            arg.clone(),
                            inf_ctx,
                        )
                    } else {
                        generate_constraints_pat(
                            body_gamma.clone(),
                            Mode::Syn,
                            arg.clone(),
                            inf_ctx,
                        )
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

            let ty_func = Type::make_arrow(ty_args, ty_body, func_node_id);
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
        PatKind::Bool(_) => {
            constrain(ty_pat, Type::make_bool(Prov::Node(pat.id)));
        }
        PatKind::Str(_) => {
            constrain(ty_pat, Type::make_string(Prov::Node(pat.id)));
        }
        PatKind::Var(identifier) => {
            dbg!(identifier);
            println!("ty_pat: {}", ty_pat);
            // letrec?: extend context with id and type before analyzing against said type
            gamma.borrow_mut().extend(identifier, ty_pat);
        }
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => Type::from_node(inf_ctx, data.id),
                None => Type::make_unit(Prov::VariantNoData(Box::new(Prov::Node(pat.id)))), // TODO BUG <---- I don't remember what this means.
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
                    // let def_type =
                    //     def_type.subst(gamma.clone(), inf_ctx, Prov::Node(pat.id), &substitution); // TODO this subst isn't necessary right?

                    let variant_def = adt_def.variants.iter().find(|v| v.ctor == *tag).unwrap();
                    let variant_data_ty = variant_def.data.clone().subst(
                        gamma.clone(),
                        inf_ctx,
                        Prov::Node(pat.id),
                        &substitution,
                    );
                    constrain(ty_data.clone(), variant_data_ty.clone());

                    def_type
                } else {
                    panic!("variant not found");
                }
            };
            println!("ty_variant: {}", ty_adt_instance);
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
            constrain(Type::make_tuple(tys_elements, pat.id), ty_pat);
            for pat in pats {
                generate_constraints_pat(gamma.clone(), Mode::Syn, pat.clone(), inf_ctx)
            }
        }
    }
}

pub fn gather_definitions_stmt(inf_ctx: &mut InferenceContext, stmt: Rc<ast::Stmt>) {
    match &*stmt.stmtkind {
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            TypeDefKind::Alias(_ident, _ty) => {}
            TypeDefKind::Adt(ident, params, variants) => {
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
                    let ast::TypeKind::Poly(ident) = &*p.typekind else { panic!("expected poly type for ADT def param") };
                    defparams.push(ident.clone());
                }
                inf_ctx.tydefs.insert(
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
        StmtKind::Expr(_expr) => {}
        StmtKind::Let((_pat, _ty_ann), _expr) => {}
        StmtKind::LetFunc(_name, _args, _out_annot, _body) => {}
    }
}

pub fn gather_definitions_toplevel(inf_ctx: &mut InferenceContext, toplevel: Rc<ast::Toplevel>) {
    for statement in toplevel.statements.iter() {
        gather_definitions_stmt(inf_ctx, statement.clone());
    }
}

pub fn generate_constraints_toplevel(
    gamma: Rc<RefCell<Gamma>>,
    toplevel: Rc<ast::Toplevel>,
    inf_ctx: &mut InferenceContext,
) -> Rc<RefCell<Gamma>> {
    for statement in toplevel.statements.iter() {
        generate_constraints_stmt(gamma.clone(), Mode::Syn, statement.clone(), inf_ctx);
    }
    gamma
}

// TODO: since each expr/pattern node has a type, the node map should be populated with the types (and errors) of each node. So node id -> {Rc<Node>, StaticsSummary}
// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub fn result_of_constraint_solving(
    inf_ctx: &InferenceContext,
    node_map: ast::NodeMap,
    source: &str,
) -> Result<(), String> {
    // TODO: you should assert that every node in the AST is in unsovled_type_suggestions_to_unknown_ty, solved or not!
    let mut type_conflicts = Vec::new();
    for potential_types in inf_ctx.vars.values() {
        // let type_suggestions = condense_candidates(potential_types);
        let type_suggestions = potential_types.clone_data().types;
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions.clone());
        }
    }

    if type_conflicts.is_empty() {
        return Ok(());
    }

    let mut err_string = String::new();
    err_string.push_str("You have a type error!\n");

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
        err_string.push_str("Type Conflict: ");
        fmt_conflicting_types(&type_conflict, &mut err_string).unwrap();
        writeln!(err_string).unwrap();
        for ty in type_conflict {
            err_string.push('\n');
            match &ty {
                Type::UnifVar(_) => err_string.push_str("Sources of unknown:\n"), // idk about this
                Type::Poly(_, _) => err_string.push_str("Sources of generic type:\n"),
                Type::DefInstance(_, ident, params) => {
                    err_string.push_str(&format!("Sources of type {}<", ident));
                    for (i, param) in params.iter().enumerate() {
                        if i != 0 {
                            err_string.push_str(", ");
                        }
                        err_string.push_str(&format!("{}", param));
                    }
                    err_string.push_str(">\n");
                }
                Type::Unit(_) => err_string.push_str("Sources of void:\n"),
                Type::Int(_) => err_string.push_str("Sources of int:\n"),
                Type::Bool(_) => err_string.push_str("Sources of bool:\n"),
                Type::String(_) => err_string.push_str("Sources of string:\n"),
                Type::Function(_, args, _) => err_string.push_str(&format!(
                    "Sources of function with {} arguments:\n",
                    args.len()
                )),
                Type::Tuple(_, elems) => err_string.push_str(&format!(
                    "Sources of tuple with {} elements:\n",
                    elems.len()
                )),
            };
            let provs = ty.provs().borrow().clone(); // TODO don't clone here
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
            });
            for cause in provs_vec {
                match cause {
                    Prov::Builtin(s) => {
                        err_string.push_str(&format!("The builtin function '{}'", s));
                    }
                    Prov::Node(id) => {
                        let span = node_map.get(id).unwrap().span();
                        err_string.push_str(&span.display(source, ""));
                    }
                    Prov::InstantiatePoly(_, ident) => {
                        err_string
                            .push_str(&format!("The instantiation of polymorphic type {ident}"));
                    }
                    Prov::FuncArg(prov, n) => {
                        match prov.as_ref() {
                            Prov::Builtin(s) => {
                                let n = n + 1; // readability
                                err_string.push_str(&format!(
                                    "--> The #{n} argument of function '{}'\n",
                                    s
                                ));
                            }
                            Prov::Node(id) => {
                                let span = node_map.get(id).unwrap().span();
                                err_string.push_str(&span.display(
                                    source,
                                    &format!("The #{n} argument of this function"),
                                ));
                            }
                            _ => unreachable!(),
                        }
                    }
                    Prov::FuncOut(prov) => match prov.as_ref() {
                        Prov::Builtin(s) => {
                            err_string.push_str(&format!(
                                "--> The output of the builtin function '{}'\n",
                                s
                            ));
                        }
                        Prov::Node(id) => {
                            let span = node_map.get(id).unwrap().span();
                            err_string
                                .push_str(&span.display(source, "The output of this function"));
                        }
                        _ => unreachable!(),
                    },
                    Prov::Alias(ident) => {
                        err_string.push_str(&format!("The type alias {ident}"));
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

    Err(err_string)
}

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Poly(_, ident) => write!(f, "{}", ident),
            Type::DefInstance(_, ident, params) => {
                write!(f, "{}<", ident)?;
                for (i, param) in params.iter().enumerate() {
                    if i != 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", param)?;
                }
                write!(f, ">")
            }
            Type::UnifVar(unifvar) => {
                let types = unifvar.clone_data().types;
                match types.len() {
                    // 0 => write!(f, "? {:#?}", unifvar),
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
            Type::Bool(_) => write!(f, "bool"),
            Type::String(_) => write!(f, "string"),
            Type::Function(_, args, out) => {
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{arg}")?;
                }
                write!(f, " -> ")?;
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

fn fmt_conflicting_types(types: &Vec<&Type>, f: &mut dyn Write) -> fmt::Result {
    let mut s = String::new();
    if types.len() > 1 {
        s.push_str("{\n");
    }
    for (i, t) in types.iter().enumerate() {
        if types.len() == 1 {
            s.push_str(&format!("{}", t));
            break;
        }
        if i == 0 {
            s.push_str(&format!("\t{}", t));
        } else {
            s.push_str(&format!("\n\t{}", t));
        }
    }
    if types.len() > 1 {
        s.push_str("\n}");
    }
    write!(f, "{}", s)
}
