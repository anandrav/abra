use crate::ast::*;
use crate::operators::BinOpcode;
use crate::types;
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

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Unknown(Id),
    Unit,
    Int,
    Bool,
    String,
    Arrow(TypeCandidates, TypeCandidates),
}

impl Type {
    pub fn fresh() -> Rc<Self> {
        Rc::new(Type::Unknown(Id::new()))
    }

    pub fn is_primitive(&self) -> bool {
        match self {
            Type::Unknown(_) => true,
            Type::Unit => true,
            Type::Int => true,
            Type::Bool => true,
            Type::String => true,
            Type::Arrow(_, _) => false,
        }
    }

    pub fn is_compound(&self) -> bool {
        !self.is_primitive()
    }

    pub fn contains_unknown(&self) -> bool {
        match self {
            Type::Unknown(_) => true,
            Type::Unit => false,
            Type::Int => false,
            Type::Bool => false,
            Type::String => false,
            Type::Arrow(t1, t2) => {
                t1.clone_data().contains_unknown() || t2.clone_data().contains_unknown()
            }
        }
    }

    pub fn of_binop(opcode: &BinOpcode) -> Rc<Self> {
        match opcode {
            BinOpcode::Add | BinOpcode::Subtract | BinOpcode::Multiply | BinOpcode::Divide => {
                Rc::new(Type::Int)
            }
            BinOpcode::Equals | BinOpcode::LessThan | BinOpcode::GreaterThan => Rc::new(Type::Bool),
        }
    }
}

impl From<Rc<types::Type>> for Type {
    fn from(t: Rc<types::Type>) -> Self {
        match &*t {
            types::Type::Unknown(id) => Type::Unknown(Id::new()),
            types::Type::Unit => Type::Unit,
            types::Type::Int => Type::Int,
            types::Type::Bool => Type::Bool,
            types::Type::String => Type::String,
            types::Type::Arrow(t1, t2) => {
                let t1 =
                    UnionFindNode::new(TypeCandidates_::singleton(Type::from(t1.clone()).into()));
                let t2 =
                    UnionFindNode::new(TypeCandidates_::singleton(Type::from(t2.clone()).into()));
                Type::Arrow(t1, t2)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct Id {
    pub id: usize,
}

impl Id {
    pub fn new() -> Self {
        static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
}

type TypeCandidates = UnionFindNode<TypeCandidates_>;

#[derive(Debug, Clone, PartialEq)]
pub struct TypeCandidates_ {
    types: Vec<Rc<Type>>,
}

impl TypeCandidates_ {
    fn singleton(t: Rc<Type>) -> Self {
        Self { types: vec![t] }
    }

    fn extend(&mut self, t_other: Rc<Type>) {
        if t_other.is_primitive() && !self.types.contains(&t_other) {
            self.types.push(t_other.clone());
        } else {
            for (i, t) in self.types.iter_mut().enumerate() {
                let t = t.clone();
                if let Type::Arrow(other_L, other_R) = &*t_other {
                    if let Type::Arrow(t_L, t_R) = &*t {
                        t_L.with_data(|t1| {
                            TypeCandidates_::merge(t_L.clone_data(), other_L.clone_data())
                        });
                        t_R.with_data(|t1| {
                            TypeCandidates_::merge(t_R.clone_data(), other_R.clone_data())
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
    let mut unknown_ty_to_candidates: Vec<(Rc<Type>, TypeCandidates)> = Vec::new();

    for constraint in constraints {
        match (&*constraint.expected, &*constraint.actual) {
            (Type::Unknown(id), t) | (t, Type::Unknown(id)) => {
                let (hole, t) = match (&*constraint.expected, &*constraint.actual) {
                    (Type::Unknown(id), t) => (constraint.expected, constraint.actual),
                    (t, Type::Unknown(id)) => (constraint.actual, constraint.expected),
                    _ => unreachable!(),
                };
                let mut hole_node = UnionFindNode::new(TypeCandidates_::singleton(hole.clone()));
                unknown_ty_to_candidates.push((hole, hole_node.clone()));
                if t.contains_unknown() {
                    let mut t_node = UnionFindNode::new(TypeCandidates_::singleton(t.clone()));
                    unknown_ty_to_candidates.push((t, t_node.clone()));
                    hole_node.union_with(&mut t_node, TypeCandidates_::merge);
                } else {
                    hole_node.with_data(|t1| t1.extend(t));
                }
            }
            _ => {}
        }
    }

    let mut unknown_ty_to_candidates_: Vec<(Rc<Type>, TypeCandidates_)> = Vec::new();

    for (unknown_ty, candidates) in unknown_ty_to_candidates {
        unknown_ty_to_candidates_.push((unknown_ty, candidates.clone_data()));
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
            match &*value.clone() {
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
        ExprKind::FuncAp(_, _, _) => unimplemented!(),
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
                Some(ty) => Rc::new(Type::from(ty.clone())),
                None => Type::fresh(),
            };
            // todo generate constraints using pattern itself as well... pattern could be a tuple or variant
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
