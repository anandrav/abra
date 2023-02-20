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
pub enum UFTypeCandidate {
    Unknown(types::Id),
    Unit,
    Int,
    Bool,
    String,
    Arrow(UFTypeCandidates, UFTypeCandidates),
}

impl UFTypeCandidate {
    pub fn is_primitive(&self) -> bool {
        match self {
            UFTypeCandidate::Unknown(_) => true,
            UFTypeCandidate::Unit => true,
            UFTypeCandidate::Int => true,
            UFTypeCandidate::Bool => true,
            UFTypeCandidate::String => true,
            UFTypeCandidate::Arrow(_, _) => false,
        }
    }

    pub fn is_compound(&self) -> bool {
        !self.is_primitive()
    }

    pub fn contains_unknown(&self) -> bool {
        match self {
            UFTypeCandidate::Unknown(_) => true,
            UFTypeCandidate::Unit => false,
            UFTypeCandidate::Int => false,
            UFTypeCandidate::Bool => false,
            UFTypeCandidate::String => false,
            UFTypeCandidate::Arrow(t1, t2) => {
                t1.clone_data().contains_unknown() || t2.clone_data().contains_unknown()
            }
        }
    }
}

// creates a UFTypeCandidates from the unknown type
// only adds/retrieves from the graph if the type is holey!
fn retrieve_and_or_add_node(
    unknown_ty_to_candidates: &mut HashMap<Rc<Type>, UFTypeCandidates>,
    unknown: Rc<Type>,
) -> UFTypeCandidates {
    if unknown_ty_to_candidates.contains_key(&unknown) {
        unknown_ty_to_candidates[&unknown].clone()
    } else {
        match &*unknown {
            Type::Unknown(id) => {
                let node = UnionFindNode::new(UFTypeCandidates_::singleton(
                    UFTypeCandidate::Unknown(id.clone()),
                ));
                unknown_ty_to_candidates.insert(unknown, node.clone());
                node
            }
            Type::Arrow(t1, t2) => {
                let t1 = retrieve_and_or_add_node(unknown_ty_to_candidates, t1.clone());
                let t2 = retrieve_and_or_add_node(unknown_ty_to_candidates, t2.clone());
                let node = UnionFindNode::new(UFTypeCandidates_::singleton(
                    UFTypeCandidate::Arrow(t1, t2),
                ));
                // unknown_ty_to_candidates.insert(unknown, node.clone());
                node
            }
            Type::Unit => UnionFindNode::new(UFTypeCandidates_::singleton(UFTypeCandidate::Unit)),
            Type::Int => UnionFindNode::new(UFTypeCandidates_::singleton(UFTypeCandidate::Int)),
            Type::Bool => UnionFindNode::new(UFTypeCandidates_::singleton(UFTypeCandidate::Bool)),
            Type::String => {
                UnionFindNode::new(UFTypeCandidates_::singleton(UFTypeCandidate::String))
            }
        }
    }
}

// TODO this should probbably be removed... or maybe not idk. Just don't create two nodes for the same unknown type...
// Maybe distinguish between nodes in the graph (holey types) and types which are not
// holey types are represented by UFTypeCandidate
// non-holey type are represented by TypeCandidate, which doesn't have Unknown case
impl From<Rc<Type>> for UFTypeCandidate {
    fn from(t: Rc<Type>) -> UFTypeCandidate {
        match &*t {
            Type::Unknown(id) => unreachable!(),
            Type::Unit => UFTypeCandidate::Unit,
            Type::Int => UFTypeCandidate::Int,
            Type::Bool => UFTypeCandidate::Bool,
            Type::String => UFTypeCandidate::String,
            Type::Arrow(t1, t2) => {
                let t1 = UnionFindNode::new(UFTypeCandidates_::singleton(
                    UFTypeCandidate::from(t1.clone()).into(),
                ));
                let t2 = UnionFindNode::new(UFTypeCandidates_::singleton(
                    UFTypeCandidate::from(t2.clone()).into(),
                ));
                UFTypeCandidate::Arrow(t1, t2)
            }
        }
    }
}

type UFTypeCandidates = UnionFindNode<UFTypeCandidates_>;

#[derive(Debug, Clone, PartialEq)]
pub enum TypeCandidate {
    Unknown(types::Id),
    Unit,
    Int,
    Bool,
    String,
    Arrow(TypeCandidates, TypeCandidates),
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeCandidates {
    types: Vec<TypeCandidate>,
}

pub fn condense_candidates(uf_type_candidates: &UFTypeCandidates) -> TypeCandidates {
    let condensed = uf_type_candidates.clone_data();
    let mut types = Vec::new();
    for candidate in &condensed.types {
        types.push(condense_candidate(candidate));
    }
    TypeCandidates { types }
}

pub fn condense_candidate(uf_type_candidate: &UFTypeCandidate) -> TypeCandidate {
    match uf_type_candidate {
        UFTypeCandidate::Unit => TypeCandidate::Unit,
        UFTypeCandidate::Int => TypeCandidate::Int,
        UFTypeCandidate::Bool => TypeCandidate::Bool,
        UFTypeCandidate::String => TypeCandidate::String,
        UFTypeCandidate::Unknown(id) => TypeCandidate::Unknown(id.clone()),
        UFTypeCandidate::Arrow(t1, t2) => {
            let t1 = condense_candidates(t1);
            let t2 = condense_candidates(t2);
            TypeCandidate::Arrow(t1, t2)
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UFTypeCandidates_ {
    types: Vec<UFTypeCandidate>,
}

impl UFTypeCandidates_ {
    fn singleton(t: UFTypeCandidate) -> Self {
        Self { types: vec![t] }
    }

    fn extend(&mut self, t_other: UFTypeCandidate) {
        if t_other.is_primitive() && !self.types.contains(&t_other) {
            self.types.push(t_other.clone());
        } else {
            let mut contains_arrow = false;
            for (i, t) in self.types.iter_mut().enumerate() {
                let t = t.clone();
                if let UFTypeCandidate::Arrow(mut other_L, mut other_R) = t_other.clone() {
                    if let UFTypeCandidate::Arrow(mut t_L, mut t_R) = t {
                        contains_arrow = true;
                        t_L.union_with(&mut other_L, UFTypeCandidates_::merge);
                        t_R.union_with(&mut other_R, UFTypeCandidates_::merge);
                    }
                }
            }
            if (!contains_arrow) {
                self.types.push(t_other.clone());
            }
        }
    }

    fn merge(first: Self, second: Self) -> Self {
        let mut merged_types = Self { types: first.types };
        for t in second.types {
            merged_types.extend(t);
        }
        merged_types
    }

    fn contains_unknown(&mut self) -> bool {
        self.types.iter().any(|t| t.contains_unknown())
    }
}

pub fn solve_constraints(constraints: Vec<Constraint>) {
    let mut constraints = constraints;
    // this is the graph, which only contains unknown types or types containing unknown types. Make a new struct for it later.
    let mut unknown_ty_to_candidates: HashMap<Rc<Type>, UFTypeCandidates> = HashMap::new();

    let mut add_hole_and_t = |hole: Rc<Type>, t: Rc<Type>| {
        let mut hole_node = retrieve_and_or_add_node(&mut unknown_ty_to_candidates, hole);
        if t.contains_unknown() {
            let mut t_node = retrieve_and_or_add_node(&mut unknown_ty_to_candidates, t);
            hole_node.union_with(&mut t_node, UFTypeCandidates_::merge);
        } else {
            hole_node.with_data(|t1| t1.extend(t.into()));
        }
    };
    while !constraints.is_empty() {
        let constraint = constraints.pop().unwrap();
        match (&*constraint.expected, &*constraint.actual) {
            (Type::Unknown(id), t) => {
                let hole = constraint.expected.clone();
                let t = constraint.actual.clone();
                add_hole_and_t(hole, t);
            }
            (t, Type::Unknown(id)) => {
                let hole = constraint.actual.clone();
                let t = constraint.expected.clone();
                add_hole_and_t(hole, t);
            }
            (Type::Arrow(t1_L, t1_R), Type::Arrow(t2_L, t2_R)) => {
                panic!("TODO: solve_constraints: (Arrow, Arrow)");
                let constraint_L = Constraint {
                    expected: t1_L.clone(),
                    actual: t2_L.clone(),
                    cause: constraint.cause.clone(),
                };
                println!("constraint_L: {:#?}", constraint_L);
                constraints.push(constraint_L);
                let constraint_R = Constraint {
                    expected: t1_R.clone(),
                    actual: t2_R.clone(),
                    cause: constraint.cause.clone(),
                };
                println!("constraint_R: {:#?}", constraint_R);
                constraints.push(constraint_R);
            }
            _ => {}
        }
    }

    let mut unknown_ty_to_candidates_: Vec<(Rc<Type>, TypeCandidates)> = Vec::new();

    for (unknown_ty, candidates) in unknown_ty_to_candidates {
        unknown_ty_to_candidates_.push((unknown_ty, condense_candidates(&candidates)));
    }

    println!(
        "unknown_ty_to_candidates_: {:#?}",
        unknown_ty_to_candidates_
    );
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
            let ty_arg = Type::fresh();
            new_ctx.borrow_mut().extend(arg1, ty_arg.clone());
            // TODO n args not just 1
            // for (arg, _) in args {
            //     new_ctx.borrow_mut().extend(arg, Type::fresh());
            // }
            let ty_body = Type::fresh();
            generate_constraints_expr(
                new_ctx,
                Mode::Ana(ty_body.clone()),
                body.clone(),
                constraints,
            );

            let ty_func = Rc::new(Type::Arrow(ty_arg, ty_body));
            match mode {
                Mode::Syn => (),
                Mode::Ana(expected) => constraints.push(Constraint {
                    expected,
                    actual: ty_func,
                    cause: expr.span.clone(),
                }),
            };
        }
        ExprKind::FuncAp(func, arg1, args) => {
            let ty_arg = Type::fresh();
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(ty_arg.clone()),
                arg1.clone(),
                constraints,
            );
            let ty_body = Type::fresh();

            let ty_func = Rc::new(Type::Arrow(ty_arg, ty_body.clone()));
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana(ty_func.clone()),
                func.clone(),
                constraints,
            );
            // TODO n args not just 1
            // for arg in args {
            //     let ty_arg = Type::fresh();
            //     generate_constraints_expr(
            //         ctx.clone(),
            //         Mode::Ana(ty_arg.clone()),
            //         arg.clone(),
            //         constraints,
            //     );
            // }
            match mode {
                Mode::Syn => (),
                Mode::Ana(expected) => constraints.push(Constraint {
                    expected,
                    actual: ty_body,
                    cause: expr.span.clone(),
                }),
            };
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
