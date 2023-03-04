use crate::ast::{self, *};
use crate::types::{types_of_binop, Prov, Type};
use disjoint_sets::UnionFindNode;
use multimap::MultiMap;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt::{self, Write};
use std::rc::Rc;

#[derive(Debug)]
pub struct Constraint {
    expected: Rc<Type>,
    actual: Rc<Type>,
    cause: Span,
}

type UFPotentialTypes = UnionFindNode<UFPotentialTypes_>;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum UFPotentialType {
    // Unknown(ast::Id),
    Unit,
    Int,
    Bool,
    String,
    Arrow(UFPotentialTypes, UFPotentialTypes),
}

impl UFPotentialType {
    pub fn is_primitive(&self) -> bool {
        match self {
            // UFPotentialType::Unknown(_) => true,
            UFPotentialType::Unit => true,
            UFPotentialType::Int => true,
            UFPotentialType::Bool => true,
            UFPotentialType::String => true,
            UFPotentialType::Arrow(_, _) => false,
        }
    }
}

// creates a UFTypeCandidates from the unknown type
// only adds/retrieves from the graph if the type is holey!
fn retrieve_and_or_add_node(
    unknown_ty_to_candidates: &mut HashMap<Rc<Type>, UFPotentialTypes>,
    unknown: Rc<Type>,
) -> UFPotentialTypes {
    if let Some(node) = unknown_ty_to_candidates.get(&unknown) {
        node.clone()
    } else {
        match &*unknown {
            Type::Unknown(_id) => {
                let node = UnionFindNode::new(UFPotentialTypes_::empty());
                unknown_ty_to_candidates.insert(unknown, node.clone());
                node
            }
            Type::Arrow(t1, t2) => {
                let t1 = retrieve_and_or_add_node(unknown_ty_to_candidates, t1.clone());
                let t2 = retrieve_and_or_add_node(unknown_ty_to_candidates, t2.clone());
                UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::Arrow(t1, t2)))
            }
            Type::Unit => UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::Unit)),
            Type::Int => UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::Int)),
            Type::Bool => UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::Bool)),
            Type::String => {
                UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::String))
            }
        }
    }
}

// TODO this should probbably be removed... or maybe not idk. Just don't create two nodes for the same unknown type...
// Maybe distinguish between nodes in the graph (holey types) and types which are not
// holey types are represented by UFTypeCandidate
// non-holey type are represented by TypeCandidate, which doesn't have Unknown case
impl From<Rc<Type>> for UFPotentialType {
    fn from(t: Rc<Type>) -> UFPotentialType {
        match &*t {
            Type::Unknown(_id) => unreachable!(),
            Type::Unit => UFPotentialType::Unit,
            Type::Int => UFPotentialType::Int,
            Type::Bool => UFPotentialType::Bool,
            Type::String => UFPotentialType::String,
            Type::Arrow(t1, t2) => {
                let t1 = UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::from(
                    t1.clone(),
                )));
                let t2 = UnionFindNode::new(UFPotentialTypes_::singleton(UFPotentialType::from(
                    t2.clone(),
                )));
                UFPotentialType::Arrow(t1, t2)
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSuggestion {
    Unknown,
    Unit,
    Int,
    Bool,
    String,
    Arrow(TypeSuggestions, TypeSuggestions),
}

impl fmt::Display for TypeSuggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeSuggestion::Unknown => write!(f, "Unknown"),
            TypeSuggestion::Unit => write!(f, "unit"),
            TypeSuggestion::Int => write!(f, "int"),
            TypeSuggestion::Bool => write!(f, "bool"),
            TypeSuggestion::String => write!(f, "string"),
            TypeSuggestion::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeSuggestions {
    types: Vec<TypeSuggestion>,
}

impl TypeSuggestions {
    pub fn solved(&self) -> bool {
        self.types.len() == 1
    }

    pub fn unsolved(&self) -> bool {
        !self.solved()
    }
}

impl fmt::Display for TypeSuggestions {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut s = String::new();
        if self.types.len() > 1 {
            s.push('{');
        }
        for (i, t) in self.types.iter().enumerate() {
            if i == 0 {
                s.push_str(&format!("{}", t));
            } else {
                s.push_str(&format!("/{}", t));
            }
        }
        if self.types.len() > 1 {
            s.push('}');
        }
        write!(f, "{}", s)
    }
}

pub fn condense_candidates(uf_type_candidates: &UFPotentialTypes) -> TypeSuggestions {
    let condensed = uf_type_candidates.clone_data();
    let mut types = Vec::new();
    for candidate in &condensed.types {
        match candidate {
            UFPotentialType::Unit => {
                let t = TypeSuggestion::Unit;
                if !types.contains(&t) {
                    types.push(t);
                }
            }
            UFPotentialType::Int => {
                let t = TypeSuggestion::Int;
                if !types.contains(&t) {
                    types.push(t);
                }
            }
            UFPotentialType::Bool => {
                let t = TypeSuggestion::Bool;
                if !types.contains(&t) {
                    types.push(t);
                }
            }
            UFPotentialType::String => {
                let t = TypeSuggestion::String;
                if !types.contains(&t) {
                    types.push(t);
                }
            }
            // UFPotentialType::Unknown(_) => (),
            UFPotentialType::Arrow(t1, t2) => {
                let t1 = condense_candidates(t1);
                let t2 = condense_candidates(t2);
                types.push(TypeSuggestion::Arrow(t1, t2));
            }
        }
    }
    if types.is_empty() {
        types.push(TypeSuggestion::Unknown);
    };
    TypeSuggestions { types }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UFPotentialTypes_ {
    types: Vec<UFPotentialType>,
}

impl UFPotentialTypes_ {
    fn empty() -> Self {
        Self { types: vec![] }
    }

    fn singleton(t: UFPotentialType) -> Self {
        Self { types: vec![t] }
    }

    // TODO cleanup:
    fn extend(&mut self, t_other: UFPotentialType) {
        if t_other.is_primitive() && !self.types.contains(&t_other) {
            self.types.push(t_other);
        } else {
            let mut contains_arrow = false;
            for (_i, t) in self.types.iter_mut().enumerate() {
                let t = t.clone();
                if let UFPotentialType::Arrow(mut other_left, mut other_right) = t_other.clone() {
                    if let UFPotentialType::Arrow(mut t_left, mut t_right) = t {
                        contains_arrow = true;
                        t_left.union_with(&mut other_left, UFPotentialTypes_::merge);
                        t_right.union_with(&mut other_right, UFPotentialTypes_::merge);
                    }
                }
            }
            if !contains_arrow {
                self.types.push(t_other);
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
}

pub fn solve_constraints(
    constraints: Vec<Constraint>,
    node_map: ast::NodeMap,
    source: &str,
) -> Result<(), String> {
    let mut constraints = constraints;
    // this is the graph, which only contains unknown types or types containing unknown types. Make a new struct for it later.
    let mut unknown_ty_to_potential_types: HashMap<Rc<Type>, UFPotentialTypes> = HashMap::new();

    let mut add_hole_and_t = |hole: Rc<Type>, t: Rc<Type>| {
        let mut hole_node = retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, hole);
        // TODO is this contains unknown check necessary?
        if t.contains_unknown() {
            let mut t_node = retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, t);
            hole_node.union_with(&mut t_node, UFPotentialTypes_::merge);
        } else {
            hole_node.with_data(|t1| t1.extend(t.into()));
        }
    };
    while !constraints.is_empty() {
        let constraint = constraints.pop().unwrap();
        match (&*constraint.expected, &*constraint.actual) {
            (Type::Unknown(_), _t) => {
                let hole = constraint.expected.clone();
                let t = constraint.actual.clone();
                add_hole_and_t(hole, t);
            }
            (_t, Type::Unknown(_)) => {
                let hole = constraint.actual.clone();
                let t = constraint.expected.clone();
                add_hole_and_t(hole, t);
            }
            (Type::Arrow(left1, right1), Type::Arrow(left2, right2)) => {
                let cause = constraint.cause;
                constraints.push(Constraint {
                    expected: left1.clone(),
                    actual: left2.clone(),
                    cause: cause.clone(),
                });
                constraints.push(Constraint {
                    expected: right1.clone(),
                    actual: right2.clone(),
                    cause,
                });
            }
            _ => {}
        }
    }

    let mut unsolved_type_suggestions_to_unknown_tys = MultiMap::new();
    for (unknown_ty, potential_types) in &unknown_ty_to_potential_types {
        let type_suggestions = condense_candidates(potential_types);
        if type_suggestions.unsolved() {
            unsolved_type_suggestions_to_unknown_tys.insert(type_suggestions, unknown_ty);
        }
    }

    if unsolved_type_suggestions_to_unknown_tys.is_empty() {
        return Ok(());
    }
    let mut err_string = String::new();
    err_string.push_str("You have a type error!\n");

    let mut ty_suggestions: Vec<(String, TypeSuggestions)> = Vec::new();

    err_string.push_str("Type Information:\n");
    for (unknown_ty, candidates) in unknown_ty_to_potential_types {
        let ast_node_str = if let Type::Unknown(prov) = &*unknown_ty {
            match prov {
                Prov::Node(id) => {
                    let span = node_map.get(id).unwrap().span();
                    source[span.lo..span.hi].to_string()
                }
                Prov::FuncArg(id, n) => {
                    let span = node_map.get(id).unwrap().span();
                    format!(
                        "argument #{} of {}",
                        n + 1,
                        source[span.lo..span.hi].to_owned()
                    )
                }
                Prov::FuncOut(id, n) => {
                    let span = node_map.get(id).unwrap().span();
                    format!(
                        "output of {} after {} arguments are passed",
                        source[span.lo..span.hi].to_owned(),
                        n
                    )
                }
            }
        } else {
            panic!("not an unknown type!");
        };
        ty_suggestions.push((ast_node_str, condense_candidates(&candidates)));
    }
    ty_suggestions.sort();
    for (ast_node_str, type_suggestions) in ty_suggestions {
        writeln!(&mut err_string, "{}: {}", ast_node_str, type_suggestions).unwrap();
    }
    Err(err_string)
}

pub struct TyCtx {
    vars: HashMap<Identifier, Rc<Type>>,
    enclosing: Option<Rc<RefCell<TyCtx>>>,
}

pub fn make_new_environment() -> Rc<RefCell<TyCtx>> {
    let ctx = TyCtx::empty();
    ctx.borrow_mut().extend(
        &String::from("print"),
        Rc::new(Type::Arrow(Rc::new(Type::String), Rc::new(Type::Unit))),
    );
    ctx.borrow_mut().extend(
        &String::from("string_of_int"),
        Rc::new(Type::Arrow(Rc::new(Type::Int), Rc::new(Type::String))),
    );
    ctx
}

// TODO reuse Environment instead of making a new struct
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
        // TODO: for these cases, we need an Unknown type for the expression node so that conflicts are discovered.
        // does subsumption play a role?
        // TODO: (tangent) since each expr/pattern node has a type, the node map should be populated with the types of each node. So node id -> {Rc<Node>, StaticsSummary}
        ExprKind::Unit => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                    cause: expr.span.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: Rc::new(Type::Unit),
                    cause: expr.span.clone(),
                });
            }
        },
        ExprKind::Int(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                    cause: expr.span.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: Rc::new(Type::Int),
                    cause: expr.span.clone(),
                });
            }
        },
        ExprKind::Bool(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                    cause: expr.span.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: Rc::new(Type::Bool),
                    cause: expr.span.clone(),
                });
            }
        },
        ExprKind::Str(_) => match mode {
            Mode::Syn => (),
            Mode::Ana(expected) => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                    cause: expr.span.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: Rc::new(Type::String),
                    cause: expr.span.clone(),
                });
            }
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
                None => match mode {
                    Mode::Syn => (),
                    Mode::Ana(expected) => constraints.push(Constraint {
                        expected,
                        actual: Type::Unknown(Prov::Node(expr.id.clone())).into(),
                        cause: expr.span.clone(),
                    }),
                },
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op);
            match mode {
                Mode::Syn => (),
                Mode::Ana(expected) => {
                    constraints.push(Constraint {
                        expected,
                        actual: ty_out,
                        cause: expr.span.clone(),
                    });
                }
            };
            generate_constraints_expr(ctx.clone(), Mode::Ana(ty_left), left.clone(), constraints);
            generate_constraints_expr(ctx, Mode::Ana(ty_right), right.clone(), constraints);
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
                None => match mode {
                    Mode::Syn => (),
                    Mode::Ana(expected) => constraints.push(Constraint {
                        expected,
                        actual: Rc::new(Type::Unit),
                        cause: expr.span.clone(),
                    }),
                },
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
        ExprKind::Func(args, _, body) => {
            let new_ctx = TyCtx::new(Some(ctx));

            let ty_args = args
                .iter()
                .map(|(arg, _)| {
                    let ty_arg = Rc::new(Type::Unknown(Prov::Node(arg.id.clone())));
                    let arg1id = arg.patkind.get_identifier();
                    new_ctx.borrow_mut().extend(&arg1id, ty_arg.clone());
                    ty_arg
                })
                .collect();

            let ty_body = Rc::new(Type::Unknown(Prov::Node(body.id.clone())));
            generate_constraints_expr(
                new_ctx,
                Mode::Ana(ty_body.clone()),
                body.clone(),
                constraints,
            );

            let ty_func = Type::make_arrow(ty_args, ty_body);
            match mode {
                Mode::Syn => (),
                Mode::Ana(expected) => constraints.push(Constraint {
                    expected,
                    actual: ty_func,
                    cause: expr.span.clone(),
                }),
            };
        }
        ExprKind::FuncAp(func, args) => {
            let tys_args: Vec<Rc<Type>> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = Rc::new(Type::Unknown(Prov::FuncArg(func.id.clone(), n as u8)));
                    generate_constraints_expr(
                        ctx.clone(),
                        Mode::Ana(unknown.clone()),
                        arg.clone(),
                        constraints,
                    );
                    unknown
                })
                .collect();

            let ty_body = Rc::new(Type::Unknown(Prov::FuncOut(
                func.id.clone(),
                tys_args.len() as u8,
            )));

            let ty_func = Type::make_arrow(tys_args, ty_body.clone());
            generate_constraints_expr(ctx, Mode::Ana(ty_func), func.clone(), constraints);
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
            let PatKind::Var(identifier) = &*pat.patkind;
            let ty_pat = match ty_opt {
                Some(ty) => ty.clone(),
                None => Rc::new(Type::Unknown(Prov::Node(pat.id.clone()))), // TODO wrong id, need id of type annotation
            };
            // todo generate constraints using pattern itself as well... pattern could be a tuple or variant, or have a type annotation?

            // letrec: extend context with id and type before analyzing against said type
            let new_ctx = TyCtx::new(Some(ctx));
            new_ctx.borrow_mut().extend(identifier, ty_pat.clone());
            generate_constraints_expr(
                new_ctx.clone(),
                Mode::Ana(ty_pat),
                expr.clone(),
                constraints,
            );
            Some(new_ctx)
        }
    }
}
