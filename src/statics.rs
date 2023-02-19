use crate::ast::*;
use crate::operators::BinOpcode;
use crate::types::{self, Type};
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

#[derive(Debug)]
pub struct Constraint {
    expected: Rc<Type>,
    actual: Rc<Type>,
    cause: Span,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum TypeCandidate {
    Unknown(types::Id),
    Unit,
    Int,
    Bool,
    String,
    Arrow(UFTypeCandidates, UFTypeCandidates),
}

impl TypeCandidate {
    pub fn is_primitive(&self) -> bool {
        match self {
            TypeCandidate::Unknown(_) => true,
            TypeCandidate::Unit => true,
            TypeCandidate::Int => true,
            TypeCandidate::Bool => true,
            TypeCandidate::String => true,
            TypeCandidate::Arrow(_, _) => false,
        }
    }

    pub fn is_compound(&self) -> bool {
        !self.is_primitive()
    }

    pub fn contains_unknown(&self) -> bool {
        match self {
            TypeCandidate::Unknown(_) => true,
            TypeCandidate::Unit => false,
            TypeCandidate::Int => false,
            TypeCandidate::Bool => false,
            TypeCandidate::String => false,
            TypeCandidate::Arrow(t1, t2) => {
                t1.clone_data().contains_unknown() || t2.clone_data().contains_unknown()
            }
        }
    }
}

impl From<Rc<Type>> for TypeCandidate {
    fn from(t: Rc<Type>) -> Self {
        match &*t {
            Type::Unknown(id) => TypeCandidate::Unknown(id.clone()),
            Type::Unit => TypeCandidate::Unit,
            Type::Int => TypeCandidate::Int,
            Type::Bool => TypeCandidate::Bool,
            Type::String => TypeCandidate::String,
            Type::Arrow(t1, t2) => {
                let t1 = UnionFindNode::new(TypeCandidates::singleton(
                    TypeCandidate::from(t1.clone()).into(),
                ));
                let t2 = UnionFindNode::new(TypeCandidates::singleton(
                    TypeCandidate::from(t2.clone()).into(),
                ));
                TypeCandidate::Arrow(t1, t2)
            }
        }
    }
}

type UFTypeCandidates = UnionFindNode<TypeCandidates>;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeCandidates {
    types: Vec<TypeCandidate>,
}

impl TypeCandidates {
    fn singleton(t: TypeCandidate) -> Self {
        Self { types: vec![t] }
    }

    fn extend(&mut self, t_other: TypeCandidate) {
        if t_other.is_primitive() && !self.types.contains(&t_other) {
            self.types.push(t_other.clone());
        } else {
            for (i, t) in self.types.iter_mut().enumerate() {
                let t = t.clone();
                if let TypeCandidate::Arrow(other_L, other_R) = &t_other {
                    if let TypeCandidate::Arrow(t_L, t_R) = &t {
                        t_L.with_data(|t1| {
                            TypeCandidates::merge(t_L.clone_data(), other_L.clone_data())
                        });
                        t_R.with_data(|t1| {
                            TypeCandidates::merge(t_R.clone_data(), other_R.clone_data())
                        });
                    }
                }
            }
        }
    }

    fn merge(first: Self, second: Self) -> Self {
        let mut merged = Self {
            types: first.types.clone(),
        };
        for t in &second.types {
            merged.extend(t.clone());
        }
        merged
    }

    fn contains_unknown(&mut self) -> bool {
        self.types.iter().any(|t| t.contains_unknown())
    }
}

pub fn solve_constraints(constraints: Vec<Constraint>) {
    let mut unknown_ty_to_candidates: HashMap<Rc<Type>, UFTypeCandidates> = HashMap::new();

    let mut add_hole_and_t = |hole: Rc<Type>, t: Rc<Type>| {
        let mut hole_node = if unknown_ty_to_candidates.contains_key(&hole) {
            unknown_ty_to_candidates[&hole].clone()
        } else {
            let hole_node = UnionFindNode::new(TypeCandidates::singleton(
                TypeCandidate::from(hole.clone()).into(),
            ));
            unknown_ty_to_candidates.insert(hole, hole_node.clone());
            hole_node
        };
        if t.contains_unknown() {
            let mut t_node = if unknown_ty_to_candidates.contains_key(&t) {
                unknown_ty_to_candidates[&t].clone()
            } else {
                let t_node = UnionFindNode::new(TypeCandidates::singleton(
                    TypeCandidate::from(t.clone()).into(),
                ));
                unknown_ty_to_candidates.insert(t, t_node.clone());
                t_node
            };
            hole_node.union_with(&mut t_node, TypeCandidates::merge);
        } else {
            hole_node.with_data(|t1| t1.extend(t.into()));
        }
    };
    for constraint in constraints {
        match (&*constraint.expected, &*constraint.actual) {
            (Type::Unknown(id), t) => {
                let hole = constraint.expected;
                let t = constraint.actual;
                add_hole_and_t(hole, t);
            }
            (t, Type::Unknown(id)) => {
                let hole = constraint.actual;
                let t = constraint.expected;
                add_hole_and_t(hole, t);
            }
            _ => {}
        }
    }

    let mut unknown_ty_to_candidates_: Vec<(TypeCandidate, TypeCandidates)> = Vec::new();

    for (unknown_ty, candidates) in unknown_ty_to_candidates {
        unknown_ty_to_candidates_.push((
            TypeCandidate::from(unknown_ty).into(),
            candidates.clone_data(),
        ));
    }

    println!("unknown_ty_to_candidates: {:#?}", unknown_ty_to_candidates_);
}

pub struct TyCtx {
    vars: HashMap<Identifier, Rc<Type>>,
    enclosing: Option<Rc<RefCell<TyCtx>>>,
}

// TODO reuse Environment instead of making a new struct
impl TyCtx {
    pub fn debug_helper(&self) -> Vec<String> {
        let mut current = Vec::new();
        for (key, value) in &self.vars {
            match &value {
                _ => current.push(key.clone()),
            }
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
}

impl fmt::Debug for TyCtx {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Environment(\n{:?}\n)", TyCtx::debug_helper(self))
    }
}

impl TyCtx {
    pub fn empty() -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            vars: HashMap::new(),
            enclosing: None,
        }))
    }

    pub fn new(enclosing: Option<Rc<RefCell<TyCtx>>>) -> Rc<RefCell<Self>> {
        Rc::new(RefCell::new(Self {
            vars: HashMap::new(),
            enclosing,
        }))
    }

    pub fn lookup(&self, id: &Identifier) -> Option<Rc<Type>> {
        match self.vars.get(id) {
            Some(typ) => Some(typ.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, id: &Identifier, typ: Rc<Type>) {
        self.vars.insert(id.clone(), typ);
    }
}

#[derive(Debug, Clone)]
pub enum Mode {
    Syn,
    Ana(Rc<Type>),
}

pub fn generate_constraints_expr(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    expr: Rc<Expr>,
    constraints: &mut Vec<Constraint>,
) {
    print!("collect_constraints: {:#?} ", expr);
    match &*expr.exprkind {
        ExprKind::Unit => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Rc::new(Type::Unit),
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Int(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Rc::new(Type::Int),
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Bool(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Rc::new(Type::Bool),
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Str(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => constraints.push(Constraint {
                expected,
                actual: Rc::new(Type::String),
                cause: expr.span.clone(),
            }),
        },
        ExprKind::Var(id) => {
            let lookup = ctx.borrow_mut().lookup(id);
            match lookup {
                Some(typ) => match mode {
                    Mode::Syn => (),
                    Mode::Ana(expected) => constraints.push(Constraint {
                        expected,
                        actual: typ,
                        cause: expr.span.clone(),
                    }),
                },
                None => panic!("Variable not found"),
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let ty_op = Type::of_binop(op);
            match mode {
                Mode::Syn => (),
                Mode::Ana(expected) => {
                    constraints.push(Constraint {
                        expected,
                        actual: ty_op.clone(),
                        cause: expr.span.clone(),
                    });
                }
            };
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(ty_op.clone()),
                left.clone(),
                constraints,
            );
            generate_constraints_expr(ctx, Mode::Ana(ty_op), right.clone(), constraints);
        }
        ExprKind::Block(statements, opt_terminal_expr) => {
            let mut new_ctx = TyCtx::new(Some(ctx));
            for statement in statements {
                let updated = generate_constraints_stmt(
                    new_ctx.clone(),
                    Mode::Syn,
                    statement.clone(),
                    constraints,
                );
                if let Some(ctx) = updated {
                    new_ctx = ctx
                }
            }
            match &opt_terminal_expr {
                Some(terminal_expr) => {
                    generate_constraints_expr(new_ctx, mode, terminal_expr.clone(), constraints)
                }
                None => (),
            };
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(Rc::new(Type::Bool)),
                cond.clone(),
                constraints,
            );
            generate_constraints_expr(ctx.clone(), mode.clone(), expr1.clone(), constraints);
            generate_constraints_expr(ctx, mode, expr2.clone(), constraints);
        }
        ExprKind::Func((arg1, _), args, _, body) => {
            let mut new_ctx = TyCtx::new(Some(ctx));
            new_ctx.borrow_mut().extend(arg1, Type::fresh());
            for (arg, _) in args {
                new_ctx.borrow_mut().extend(arg, Type::fresh());
            }
            generate_constraints_expr(new_ctx, Mode::Syn, body.clone(), constraints);
        }
        ExprKind::FuncAp(func, arg1, args) => {
            let ty_func = Type::fresh();
            let ty_arg = Type::fresh();
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(ty_func.clone()),
                func.clone(),
                constraints,
            );
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(ty_arg.clone()),
                arg1.clone(),
                constraints,
            );
            for arg in args {
                let ty_arg = Type::fresh();
                generate_constraints_expr(
                    ctx.clone(),
                    Mode::Ana(ty_arg.clone()),
                    arg.clone(),
                    constraints,
                );
            }
            match mode {
                Mode::Syn => (),
                Mode::Ana(expected) => constraints.push(Constraint {
                    expected,
                    actual: ty_func,
                    cause: expr.span.clone(),
                }),
            };
        }
        _ => {
            panic!("expr: {:#?}", expr);
            unimplemented!()
        }
    }
}

pub fn generate_constraints_stmt(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    stmt: Rc<Stmt>,
    constraints: &mut Vec<Constraint>,
) -> Option<Rc<RefCell<TyCtx>>> {
    match &*stmt.stmtkind {
        StmtKind::Expr(expr) => {
            generate_constraints_expr(ctx, mode, expr.clone(), constraints);
            None
        }
        StmtKind::Let(pat, ty_opt, expr) => {
            let identifier = match &*pat.patkind {
                PatKind::Var(identifier) => identifier,
                _ => unimplemented!(),
            };
            let ty_pat = match ty_opt {
                Some(ty) => ty.clone(),
                None => Type::fresh(),
            };
            // todo generate constraints using pattern itself as well... pattern could be a tuple or variant, or have a type annotation?
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(ty_pat.clone()),
                expr.clone(),
                constraints,
            );
            let new_ctx = TyCtx::new(Some(ctx));
            new_ctx.borrow_mut().extend(identifier, ty_pat);
            Some(new_ctx)
        }
    }
}
