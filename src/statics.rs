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

    // valid solutions
    Poly(Provs, Identifier),
    Unit(Provs),
    Int(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<Type>, Box<Type>),
    Tuple(Provs, Vec<Type>),
    Adt(Provs, Identifier, Vec<Variant>),

    // incomplete solutions
    Variants(Provs, Vec<Variant>), // "some Adt which has these variants, and maybe more"
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
    Poly, // TODO: why isn't the Identifier included here?
    Unit,
    Int,
    Bool,
    String,
    Arrow(u8), // u8 represents the number of arguments
    Tuple(u8), // u8 represents the number of elements
    Adt(Identifier),
    Variants,
}

// Provenances are used to:
// (1) track the origins (plural!) of a type solution
// (2) give the *unique* identity of an unknown type variable (UnifVar) in the SolutionMap
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Prov {
    Node(ast::Id), // the type of an expression or statement
    Alias(Identifier),
    Variant(Identifier),
    Builtin(String), // a builtin function or constant, which doesn't exist in the AST
    InstantiatePoly(Box<Prov>, Identifier),
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
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
            Type::Adt(_, ident, _) => Some(TypeKey::Adt(ident.clone())),
            Type::Variants(_, _) => Some(TypeKey::Variants),
        }
    }

    // Creates a clone of a Type with polymorphic variables not in scope replaced with fresh unification variables
    // Cloning type variables is very subtle...
    pub fn instantiate(
        self,
        ctx: Rc<RefCell<TyCtx>>,
        solution_map: &mut SolutionMap,
        prov: Prov,
    ) -> Type {
        match self {
            Type::Unit(_) | Type::Int(_) | Type::Bool(_) | Type::String(_) => {
                self // noop
            }
            Type::UnifVar(unifvar) => {
                let data = unifvar.clone_data();
                if data.types.len() == 1 {
                    // TODO consider relaxing this if it gives better editor feedback. But test thoroughly after
                    let ty = data.types.into_values().next().unwrap();
                    if let Type::Poly(_, _) = ty {
                        ty.instantiate(ctx, solution_map, prov)
                    } else {
                        let ty = ty.instantiate(ctx, solution_map, prov.clone());
                        let mut types = BTreeMap::new();
                        types.insert(ty.key().unwrap(), ty);
                        let data = UnifVarData { types };
                        let unifvar = UnionFindNode::new(data);
                        solution_map.insert(prov, unifvar.clone());
                        Type::UnifVar(unifvar) // TODO clone this? But test thoroughly after lol
                    }
                } else {
                    Type::UnifVar(unifvar) // noop
                }
            }
            Type::Poly(_, ref ident) => {
                if !ctx.borrow().lookup_poly(ident) {
                    Type::fresh_unifvar(
                        solution_map,
                        Prov::InstantiatePoly(Box::new(prov), ident.clone()),
                    )
                } else {
                    self // noop
                }
            }
            Type::Function(provs, args, out) => {
                let args = args
                    .into_iter()
                    .map(|ty| ty.instantiate(ctx.clone(), solution_map, prov.clone()))
                    .collect();
                let out = Box::new(out.instantiate(ctx, solution_map, prov));
                Type::Function(provs, args, out)
            }
            Type::Tuple(provs, elems) => {
                let elems = elems
                    .into_iter()
                    .map(|ty| ty.instantiate(ctx.clone(), solution_map, prov.clone()))
                    .collect();
                Type::Tuple(provs, elems)
            }
            Type::Adt(provs, ident, variants) => {
                let variants = variants
                    .into_iter()
                    .map(|variant| Variant {
                        ctor: variant.ctor,
                        data: variant
                            .data
                            .instantiate(ctx.clone(), solution_map, prov.clone()),
                    })
                    .collect();
                Type::Adt(provs, ident, variants)
            }
            Type::Variants(provs, variants) => {
                let variants = variants
                    .into_iter()
                    .map(|variant| Variant {
                        ctor: variant.ctor,
                        data: variant
                            .data
                            .instantiate(ctx.clone(), solution_map, prov.clone()),
                    })
                    .collect();
                Type::Variants(provs, variants)
            }
        }
    }

    pub fn from_node(solution_map: &mut SolutionMap, id: ast::Id) -> Type {
        let prov = Prov::Node(id);
        Type::fresh_unifvar(solution_map, prov)
    }

    pub fn fresh_unifvar(solution_map: &mut SolutionMap, prov: Prov) -> Type {
        match solution_map.get(&prov) {
            Some(ty) => Type::UnifVar(ty.clone()),
            None => {
                let ty_var = UnifVar::new(UnifVarData::empty());
                let ty = Type::UnifVar(ty_var.clone());
                solution_map.insert(prov, ty_var);
                ty
            }
        }
    }

    pub fn make_poly(prov: Prov, ident: String) -> Type {
        Type::Poly(provs_singleton(prov), ident)
    }

    pub fn make_adt(ident: String, variants: Vec<Variant>, id: ast::Id) -> Type {
        Type::Adt(provs_singleton(Prov::Node(id)), ident, variants)
    }

    pub fn make_variant(ctor: Identifier, data: Type, id: ast::Id) -> Type {
        Type::Variants(
            provs_singleton(Prov::Node(id)),
            vec![Variant { ctor, data }],
        )
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
            | Self::Adt(provs, _, _)
            | Self::Variants(provs, _) => provs,
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
    solution_map: &mut SolutionMap,
    ast_type: Rc<ast::AstType>,
) -> Type {
    match &*ast_type.typekind {
        ast::TypeKind::Poly(ident) => Type::make_poly(Prov::Node(ast_type.id()), ident.clone()),
        ast::TypeKind::Alias(ident) => {
            Type::fresh_unifvar(solution_map, Prov::Alias(ident.clone()))
        }
        ast::TypeKind::Unit => Type::make_unit(Prov::Node(ast_type.id())),
        ast::TypeKind::Int => Type::make_int(Prov::Node(ast_type.id())),
        ast::TypeKind::Bool => Type::make_bool(Prov::Node(ast_type.id())),
        ast::TypeKind::Str => Type::make_string(Prov::Node(ast_type.id())),
        // TODO wait does this only allow one argument??
        ast::TypeKind::Arrow(lhs, rhs) => Type::make_arrow(
            vec![ast_type_to_statics_type(solution_map, lhs.clone())],
            ast_type_to_statics_type(solution_map, rhs.clone()),
            ast_type.id(),
        ),
        ast::TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_statics_type(solution_map, t.clone()));
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

pub type SolutionMap = HashMap<Prov, UnifVar>;

impl UnifVarData {
    fn empty() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    // TODO: occurs check
    fn extend(&mut self, t_other: Type) {
        let key = t_other.key().unwrap();
        match key {
            TypeKey::Variants | TypeKey::Adt(_) => {
                let mut lookup: Vec<_> = self
                    .types
                    .iter_mut()
                    .filter(|(k, _)| matches!(k, TypeKey::Variants | TypeKey::Adt(_)))
                    .collect();
                if lookup.is_empty() {
                    // conflict
                    self.types.insert(key, t_other);
                    return;
                }

                if lookup.len() > 1 {
                    for (_k, ref mut t) in lookup {
                        if let Type::Adt(provs, _, variants) = &t {
                            if let Type::Variants(provs, other_variants) = &t_other {
                                t.provs().borrow_mut().extend(provs.borrow().clone())
                            }
                        }
                    }
                    return;
                }

                let (k, ref mut t) = lookup[0];
                match &t_other {
                    Type::Adt(other_provs, other_identifier, other_variants) => {
                        match &t {
                            Type::Adt(_, identifier, variants) => {
                                println!("ADT CONFLICT?");
                                dbg!(t.clone());
                                dbg!(t_other.clone());
                                if identifier == other_identifier && variants == other_variants {
                                    println!("no conflict");
                                    // no conflict
                                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                                } else {
                                    println!("conflict!");
                                    // conflict
                                    self.types.insert(key, t_other); // BUG! getting replaced
                                }
                            }
                            Type::Variants(_, variants) => {
                                let mut conflict = false;
                                for variant in variants {
                                    if !other_variants.iter().any(|v| v.ctor == variant.ctor) {
                                        conflict = true;
                                        break;
                                    }
                                }

                                if conflict {
                                    self.types.insert(key, t_other);
                                } else {
                                    // no conflict
                                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                                }
                            }
                            _ => panic!("should be Adt or Variants for key Adt"),
                        }
                    }
                    Type::Variants(other_provs, other_variants) => {
                        match t {
                            Type::Adt(_, identifier, variants) => {
                                // println!("variants: {:?}", variants);
                                // println!("other_variants: {:?}", other_variants);
                                let mut conflict = false;
                                for other_variant in other_variants {
                                    if !variants.iter().any(|v| v.ctor == other_variant.ctor) {
                                        conflict = true;
                                        break;
                                    }
                                }

                                if conflict {
                                    // println!("there was a conflict :(");
                                    self.types.insert(key, t_other);
                                } else {
                                    // println!("there wasn't a conflict");
                                    // no conflict
                                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                                }
                            }
                            Type::Variants(_, ref mut variants) => {
                                // no conflict
                                for other_variant in other_variants {
                                    if !variants.iter().any(|v| v.ctor == other_variant.ctor) {
                                        variants.push(other_variant.clone());
                                    }
                                }
                                t.provs().borrow_mut().extend(other_provs.borrow().clone())
                            }
                            _ => panic!("should be Adt or Variants"),
                        }
                    }
                    _ => panic!("should be Adt or Variants"),
                }

                return;
            }
            _ => {}
        }
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
                        }
                    }
                }
                _ => {}
            }
        } else {
            // conflict
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

pub struct TyCtx {
    pub vars: HashMap<Identifier, Type>,
    poly_type_vars: HashSet<Identifier>,
    enclosing: Option<Rc<RefCell<TyCtx>>>,
}

pub fn make_new_environment() -> Rc<RefCell<TyCtx>> {
    let ctx = TyCtx::empty();
    ctx.borrow_mut().extend(
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
    ctx.borrow_mut().extend(
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
    ctx
}

impl fmt::Debug for TyCtx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:?}\n)", TyCtx::debug_helper(self))
    }
}

impl TyCtx {
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

    pub fn new(enclosing: Option<Rc<RefCell<TyCtx>>>) -> Rc<RefCell<Self>> {
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
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    expr: Rc<Expr>,
    solution_map: &mut SolutionMap,
) {
    let node_ty = Type::from_node(solution_map, expr.id);
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
            let lookup = ctx.borrow_mut().lookup(id);
            if let Some(typ) = lookup {
                // replace polymorphic types with unifvars if necessary
                let typ = typ.instantiate(ctx, solution_map, Prov::Node(expr.id));
                constrain(typ, node_ty);
            } else {
                panic!("variable not bound in TyCtx: {}", id);
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op, expr.id);
            constrain(ty_out, node_ty);
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana { expected: ty_left },
                left.clone(),
                solution_map,
            );
            generate_constraints_expr(
                ctx,
                Mode::Ana { expected: ty_right },
                right.clone(),
                solution_map,
            );
        }
        ExprKind::Block(statements) => {
            if statements.is_empty() {
                constrain(node_ty, Type::make_unit(Prov::Node(expr.id)));
                return;
            }
            let new_ctx = TyCtx::new(Some(ctx));
            for statement in statements[..statements.len() - 1].iter() {
                generate_constraints_stmt(
                    new_ctx.clone(),
                    Mode::Syn,
                    statement.clone(),
                    solution_map,
                );
            }
            // if last statement is an expression, the block will have that expression's type
            if let StmtKind::Expr(terminal_expr) = &*statements.last().unwrap().stmtkind {
                generate_constraints_expr(
                    new_ctx,
                    Mode::Ana { expected: node_ty },
                    terminal_expr.clone(),
                    solution_map,
                )
            } else {
                constrain(node_ty, Type::make_unit(Prov::Node(expr.id)))
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: Type::make_bool(Prov::Node(cond.id)),
                },
                cond.clone(),
                solution_map,
            );
            match &expr2 {
                // if-else
                Some(expr2) => {
                    generate_constraints_expr(
                        ctx.clone(),
                        Mode::Ana {
                            expected: node_ty.clone(),
                        },
                        expr1.clone(),
                        solution_map,
                    );
                    generate_constraints_expr(
                        ctx,
                        Mode::Ana { expected: node_ty },
                        expr2.clone(),
                        solution_map,
                    );
                }
                // just if
                None => {
                    generate_constraints_expr(
                        ctx,
                        Mode::Ana {
                            expected: Type::make_unit(Prov::Node(expr.id)),
                        },
                        expr1.clone(),
                        solution_map,
                    );
                    constrain(node_ty, Type::make_unit(Prov::Node(expr.id)))
                }
            }
        }
        ExprKind::Match(expr, arms) => {
            let ty_scrutiny = Type::from_node(solution_map, expr.id);
            for arm in arms {
                let new_ctx = TyCtx::new(Some(ctx.clone()));
                generate_constraints_pat(
                    new_ctx.clone(),
                    Mode::Ana {
                        expected: ty_scrutiny.clone(),
                    },
                    arm.pat.clone(),
                    solution_map,
                );
                generate_constraints_expr(
                    new_ctx,
                    Mode::Ana {
                        expected: node_ty.clone(),
                    },
                    arm.expr.clone(),
                    solution_map,
                );
            }
        }
        ExprKind::Func(args, out_annot, body) => {
            let (ty_func, _body_ctx) = generate_constraints_function_helper(
                ctx,
                solution_map,
                args,
                out_annot,
                body,
                expr.id,
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
                        solution_map,
                        Prov::FuncArg(Box::new(Prov::Node(func.id)), n as u8),
                    );
                    generate_constraints_expr(
                        ctx.clone(),
                        Mode::Ana {
                            expected: unknown.clone(),
                        },
                        arg.clone(),
                        solution_map,
                    );
                    unknown
                })
                .collect();

            // body
            let ty_body =
                Type::fresh_unifvar(solution_map, Prov::FuncOut(Box::new(Prov::Node(func.id))));
            constrain(ty_body.clone(), node_ty);

            // function type
            let ty_func = Type::make_arrow(tys_args, ty_body, expr.id);
            generate_constraints_expr(
                ctx,
                Mode::Ana { expected: ty_func },
                func.clone(),
                solution_map,
            );
        }
        ExprKind::Tuple(exprs) => {
            let tys = exprs
                .iter()
                .map(|expr| Type::fresh_unifvar(solution_map, Prov::Node(expr.id)))
                .collect();
            constrain(Type::make_tuple(tys, expr.id), node_ty);
            for expr in exprs {
                generate_constraints_expr(ctx.clone(), Mode::Syn, expr.clone(), solution_map);
            }
        }
    }
}

// helper function for common code between Expr::Func and Expr::LetFunc
pub fn generate_constraints_function_helper(
    ctx: Rc<RefCell<TyCtx>>,
    solution_map: &mut SolutionMap,
    args: &[(Rc<ast::Pat>, Option<Rc<ast::AstType>>)],
    out_annot: &Option<Rc<ast::AstType>>,
    body: &Rc<Expr>,
    func_node_id: ast::Id,
) -> (Type, Rc<RefCell<TyCtx>>) {
    // arguments
    let body_ctx = TyCtx::new(Some(ctx));
    let ty_args = args
        .iter()
        .map(|(arg, arg_annot)| {
            let ty_pat = Type::from_node(solution_map, arg.id);
            if let Some(arg_annot) = arg_annot {
                let arg_annot = ast_type_to_statics_type(solution_map, arg_annot.clone());
                body_ctx.borrow_mut().add_polys(&arg_annot);
                generate_constraints_pat(
                    body_ctx.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                    Mode::Ana {
                        expected: arg_annot,
                    },
                    arg.clone(),
                    solution_map,
                )
            } else {
                generate_constraints_pat(body_ctx.clone(), Mode::Syn, arg.clone(), solution_map)
            }
            ty_pat
        })
        .collect();

    // body
    let ty_body = Type::fresh_unifvar(
        solution_map,
        Prov::FuncOut(Box::new(Prov::Node(func_node_id))),
    );
    generate_constraints_expr(
        body_ctx.clone(),
        Mode::Ana {
            expected: ty_body.clone(),
        },
        body.clone(),
        solution_map,
    );
    if let Some(out_annot) = out_annot {
        let out_annot = ast_type_to_statics_type(solution_map, out_annot.clone());
        body_ctx.borrow_mut().add_polys(&out_annot);
        generate_constraints_expr(
            body_ctx.clone(),
            Mode::Ana {
                expected: out_annot,
            },
            body.clone(),
            solution_map,
        );
    }

    (Type::make_arrow(ty_args, ty_body, func_node_id), body_ctx)
}

pub fn generate_constraints_stmt(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    stmt: Rc<Stmt>,
    solution_map: &mut SolutionMap,
) {
    match &*stmt.stmtkind {
        StmtKind::TypeDef(typdefkind) => match &**typdefkind {
            // TODO: make Alias and Adt separate StmtKinds... nesting is unnecessary
            TypeDefKind::Alias(ident, ty) => {
                let left = Type::fresh_unifvar(solution_map, Prov::Alias(ident.clone()));
                let right = ast_type_to_statics_type(solution_map, ty.clone());
                constrain(left, right);
            }
            TypeDefKind::Adt(ident, variants) => {
                let ty_node = Type::fresh_unifvar(solution_map, Prov::Node(stmt.id));
                let mut tys_variants = vec![];
                for variant in variants {
                    constrain(
                        ty_node.clone(),
                        Type::fresh_unifvar(solution_map, Prov::Variant(variant.ctor.clone())),
                    );
                    ctx.borrow_mut().extend(&variant.ctor, ty_node.clone());
                    let data = match &variant.data {
                        Some(data) => ast_type_to_statics_type(solution_map, data.clone()),
                        None => Type::make_unit(Prov::Node(variant.id())),
                    };
                    tys_variants.push(Variant {
                        ctor: variant.ctor.clone(),
                        data,
                    });
                }
                constrain(
                    ty_node,
                    Type::make_adt(ident.clone(), tys_variants, stmt.id),
                );
            }
        },
        StmtKind::Expr(expr) => {
            generate_constraints_expr(ctx, mode, expr.clone(), solution_map);
        }
        StmtKind::Let((pat, ty_ann), expr) => {
            let ty_pat = Type::from_node(solution_map, pat.id);

            if let Some(ty_ann) = ty_ann {
                let ty_ann = ast_type_to_statics_type(solution_map, ty_ann.clone());
                ctx.borrow_mut().add_polys(&ty_ann);
                generate_constraints_pat(
                    ctx.clone(),
                    Mode::Ana { expected: ty_ann },
                    pat.clone(),
                    solution_map,
                )
            } else {
                generate_constraints_pat(ctx.clone(), Mode::Syn, pat.clone(), solution_map)
            };

            generate_constraints_expr(
                ctx,
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                solution_map,
            );
        }
        StmtKind::LetFunc(name, args, out_annot, body) => {
            let func_node_id = stmt.id;

            let ty_pat = Type::from_node(solution_map, name.id);
            ctx.borrow_mut()
                .extend(&name.patkind.get_identifier_of_variable(), ty_pat.clone());

            let body_ctx = TyCtx::new(Some(ctx));

            // BEGIN TODO use helper function for functions again

            // arguments
            let ty_args = args
                .iter()
                .map(|(arg, arg_annot)| {
                    let ty_pat = Type::from_node(solution_map, arg.id);
                    if let Some(arg_annot) = arg_annot {
                        let arg_annot = ast_type_to_statics_type(solution_map, arg_annot.clone());
                        body_ctx.borrow_mut().add_polys(&arg_annot);
                        generate_constraints_pat(
                            body_ctx.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                            Mode::Ana {
                                expected: arg_annot,
                            },
                            arg.clone(),
                            solution_map,
                        )
                    } else {
                        generate_constraints_pat(
                            body_ctx.clone(),
                            Mode::Syn,
                            arg.clone(),
                            solution_map,
                        )
                    }
                    ty_pat
                })
                .collect();

            // body
            let ty_body = Type::fresh_unifvar(
                solution_map,
                Prov::FuncOut(Box::new(Prov::Node(func_node_id))),
            );
            generate_constraints_expr(
                body_ctx.clone(),
                Mode::Ana {
                    expected: ty_body.clone(),
                },
                body.clone(),
                solution_map,
            );
            if let Some(out_annot) = out_annot {
                let out_annot = ast_type_to_statics_type(solution_map, out_annot.clone());
                body_ctx.borrow_mut().add_polys(&out_annot);
                generate_constraints_expr(
                    body_ctx,
                    Mode::Ana {
                        expected: out_annot,
                    },
                    body.clone(),
                    solution_map,
                );
            }

            let ty_func = Type::make_arrow(ty_args, ty_body, func_node_id);
            // END TODO use helper function for functions again

            constrain(ty_pat, ty_func);
        }
    }
}

pub fn generate_constraints_pat(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    pat: Rc<Pat>,
    solution_map: &mut SolutionMap,
) {
    let ty_pat = Type::from_node(solution_map, pat.id);
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => constrain(expected, ty_pat.clone()),
    };
    match &*pat.patkind {
        PatKind::Var(identifier) => {
            // letrec?: extend context with id and type before analyzing against said type
            let ty_pat = Type::from_node(solution_map, pat.id);
            ctx.borrow_mut().extend(identifier, ty_pat);
        }
        PatKind::Variant(tag, data) => {
            let ty_data = match data {
                Some(data) => Type::from_node(solution_map, data.id),
                None => Type::make_unit(Prov::Node(pat.id)),
            };
            let ty_some_variant = Type::fresh_unifvar(solution_map, Prov::Variant(tag.clone()));
            let ty_variant = Type::make_variant(tag.clone(), ty_data, pat.id);
            constrain(ty_pat.clone(), ty_some_variant);
            constrain(ty_pat, ty_variant);
            if let Some(data) = data {
                generate_constraints_pat(ctx, Mode::Syn, data.clone(), solution_map)
            };
        }
        PatKind::Tuple(pats) => {
            let tys_elements = pats
                .iter()
                .map(|pat| Type::fresh_unifvar(solution_map, Prov::Node(pat.id)))
                .collect();
            constrain(Type::make_tuple(tys_elements, pat.id), ty_pat);
            for pat in pats {
                generate_constraints_pat(ctx.clone(), Mode::Syn, pat.clone(), solution_map)
            }
        }
    }
}

pub fn generate_constraints_toplevel(
    ctx: Rc<RefCell<TyCtx>>,
    toplevel: Rc<ast::Toplevel>,
    solution_map: &mut SolutionMap,
) -> Rc<RefCell<TyCtx>> {
    for statement in toplevel.statements.iter() {
        generate_constraints_stmt(ctx.clone(), Mode::Syn, statement.clone(), solution_map);
    }
    ctx
}

// TODO: since each expr/pattern node has a type, the node map should be populated with the types (and errors) of each node. So node id -> {Rc<Node>, StaticsSummary}
// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub fn result_of_constraint_solving(
    solution_map: SolutionMap,
    node_map: ast::NodeMap,
    source: &str,
) -> Result<(), String> {
    // TODO: you should assert that every node in the AST is in unsovled_type_suggestions_to_unknown_ty, solved or not!
    let mut type_conflicts = Vec::new();
    for potential_types in solution_map.values() {
        // let type_suggestions = condense_candidates(potential_types);
        let type_suggestions = potential_types.clone_data().types;
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions.clone());
        }
        if type_suggestions.len() == 1 {
            if let Type::Variants(_, _) = type_suggestions.values().next().unwrap() {
                type_conflicts.push(type_suggestions);
            }
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
                Type::Adt(_, ident, _) => {
                    err_string.push_str(&format!("Sources of enum {ident}:\n"))
                }
                Type::Variants(_, variants) => err_string
                    .push_str(&format!("Sources of enum with variants: {:#?}\n", variants)),
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
                Prov::Variant(_) => 6,
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
                    Prov::Variant(ident) => {
                        err_string.push_str(&format!("The enum variant {ident}"));
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
            Type::UnifVar(unifvar) => {
                let types = unifvar.clone_data().types;
                match types.len() {
                    0 => write!(f, "?"),
                    1 => write!(f, "{}", types.values().next().unwrap()),
                    _ => write!(f, "!"),
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
            Type::Adt(_, ident, _) => {
                write!(f, "{}", ident)
            }
            Type::Variants(_, variants) => {
                write!(f, "enum {{")?;
                for (i, variant) in variants.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}", variant)?;
                }
                write!(f, "}}")
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
