use crate::ast::{self, *};
use crate::types::{types_of_binop, Prov, Type};
use disjoint_sets::UnionFindNode;
use multimap::MultiMap;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self};
use std::rc::Rc;

#[derive(Debug)]
pub struct Constraint {
    expected: Rc<Type>,
    expected_origin: Option<ast::Id>,
    actual: Rc<Type>,
    actual_origin: Option<ast::Id>,
}

type UFPotentialTypes = UnionFindNode<UFPotentialTypes_>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum PotentialTypeCtor {
    Unit,
    Int,
    Bool,
    String,
    Arrow,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UFPotentialType {
    // TODO: don't store Ctor in Primitive/Binary, it's already the key of the map.
    Primitive(PotentialTypeCtor, ConstraintCauses),
    Binary(
        PotentialTypeCtor,
        ConstraintCauses,
        UFPotentialTypes,
        UFPotentialTypes,
    ),
}

impl UFPotentialType {
    pub fn causes(&self) -> &ConstraintCauses {
        match &self {
            Self::Primitive(_, causes) => causes,
            Self::Binary(_, causes, _, _) => causes,
        }
    }

    pub fn causes_mut(&mut self) -> &mut ConstraintCauses {
        match self {
            Self::Primitive(_, causes) => causes,
            Self::Binary(_, causes, _, _) => causes,
        }
    }
}

pub type ConstraintCauses = BTreeSet<ast::Id>;

// creates a UFTypeCandidates from the unknown type
// only adds/retrieves from the graph if the type is holey!
fn retrieve_and_or_add_node(
    unknown_ty_to_candidates: &mut HashMap<Prov, UFPotentialTypes>,
    unknown: Rc<Type>,
    cause: Option<ast::Id>,
) -> UFPotentialTypes {
    let causes_single = match cause {
        Some(cause) => {
            let mut set = BTreeSet::new();
            set.insert(cause);
            set
        }
        None => BTreeSet::new(),
    };
    match &*unknown {
        Type::Unknown(prov) => {
            if let Some(node) = unknown_ty_to_candidates.get(prov) {
                node.clone()
            } else {
                let node = UnionFindNode::new(UFPotentialTypes_::empty());
                unknown_ty_to_candidates.insert(prov.clone(), node.clone());
                node
            }
        }
        Type::Arrow(t1, t2) => {
            let t1 = retrieve_and_or_add_node(unknown_ty_to_candidates, t1.clone(), None);
            let t2 = retrieve_and_or_add_node(unknown_ty_to_candidates, t2.clone(), None);
            UnionFindNode::new(UFPotentialTypes_::singleton(
                PotentialTypeCtor::Arrow,
                UFPotentialType::Binary(PotentialTypeCtor::Arrow, causes_single, t1, t2),
            ))
        }
        Type::Unit => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Unit,
            UFPotentialType::Primitive(PotentialTypeCtor::Unit, causes_single),
        )),
        Type::Int => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Int,
            UFPotentialType::Primitive(PotentialTypeCtor::Int, causes_single),
        )),
        Type::Bool => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Bool,
            UFPotentialType::Primitive(PotentialTypeCtor::Bool, causes_single),
        )),
        Type::String => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::String,
            UFPotentialType::Primitive(PotentialTypeCtor::String, causes_single),
        )),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSuggestion {
    Unknown,
    Unit(ConstraintCauses),
    Int(ConstraintCauses),
    Bool(ConstraintCauses),
    String(ConstraintCauses),
    Arrow(TypeSuggestions, TypeSuggestions),
}

impl fmt::Display for TypeSuggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeSuggestion::Unknown => write!(f, "Unknown"),
            TypeSuggestion::Unit(_) => write!(f, "unit"),
            TypeSuggestion::Int(_) => write!(f, "int"),
            TypeSuggestion::Bool(_) => write!(f, "bool"),
            TypeSuggestion::String(_) => write!(f, "string"),
            TypeSuggestion::Arrow(t1, t2) => write!(f, "({} -> {})", t1, t2),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TypeSuggestions {
    types: BTreeSet<TypeSuggestion>,
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
    let mut types: BTreeSet<TypeSuggestion> = BTreeSet::new();
    for (ctor, potential_type) in &condensed.types {
        match (ctor, potential_type) {
            (PotentialTypeCtor::Unit, _) => {
                let t = TypeSuggestion::Unit(potential_type.causes().clone());
                types.insert(t);
            }
            (PotentialTypeCtor::Int, _) => {
                let t = TypeSuggestion::Int(potential_type.causes().clone());
                types.insert(t);
            }
            (PotentialTypeCtor::Bool, _) => {
                let t = TypeSuggestion::Bool(potential_type.causes().clone());
                types.insert(t);
            }
            (PotentialTypeCtor::String, _) => {
                let t = TypeSuggestion::String(potential_type.causes().clone());
                types.insert(t);
            }
            (
                PotentialTypeCtor::Arrow,
                // TODO: use the causes from the Arrow potential type
                UFPotentialType::Binary(PotentialTypeCtor::Arrow, _causes, t1, t2),
            ) => {
                let t1 = condense_candidates(t1);
                let t2 = condense_candidates(t2);
                types.insert(TypeSuggestion::Arrow(t1, t2));
            }
            _ => unreachable!(),
        }
    }
    if types.is_empty() {
        types.insert(TypeSuggestion::Unknown);
    };
    TypeSuggestions { types }
}

#[derive(Debug, Clone, PartialEq)]
pub struct UFPotentialTypes_ {
    types: BTreeMap<PotentialTypeCtor, UFPotentialType>,
}

impl UFPotentialTypes_ {
    fn empty() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    fn singleton(ctor: PotentialTypeCtor, t: UFPotentialType) -> Self {
        Self {
            types: {
                let mut s = BTreeMap::new();
                s.insert(ctor, t);
                s
            },
        }
    }

    fn extend(&mut self, ctor: PotentialTypeCtor, mut t_other: UFPotentialType) {
        if let Some(mut t) = self.types.get_mut(&ctor) {
            match t_other {
                UFPotentialType::Primitive(_, other_causes) => {
                    t.causes_mut().extend(other_causes);
                }
                UFPotentialType::Binary(
                    PotentialTypeCtor::Arrow,
                    other_causes,
                    ref mut other_left,
                    ref mut other_right,
                ) => match &mut t {
                    UFPotentialType::Binary(
                        PotentialTypeCtor::Arrow,
                        t_causes,
                        ref mut t_left,
                        ref mut t_right,
                    ) => {
                        t_causes.extend(other_causes);
                        t_left.union_with(other_left, UFPotentialTypes_::merge);
                        t_right.union_with(other_right, UFPotentialTypes_::merge);
                    }
                    _ => unreachable!("should be binary"),
                },
                _ => unreachable!("ctor of binary should be arrow"),
            }
        } else {
            self.types.insert(ctor, t_other);
        }
    }

    fn merge(first: Self, second: Self) -> Self {
        let mut merged_types = Self { types: first.types };
        for (ctor, t) in second.types {
            merged_types.extend(ctor, t);
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
    let mut unknown_ty_to_potential_types: HashMap<Prov, UFPotentialTypes> = HashMap::new();

    let mut add_hole_and_t = |hole: Rc<Type>, t: Rc<Type>, cause: Option<ast::Id>| {
        let mut hole_node =
            retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, hole, None);
        let mut t_node = retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, t, cause);
        hole_node.union_with(&mut t_node, UFPotentialTypes_::merge);
    };
    while !constraints.is_empty() {
        let constraint = constraints.pop().unwrap();
        match (&*constraint.expected, &*constraint.actual) {
            (Type::Unknown(_), _t) => {
                let hole = constraint.expected.clone();
                let t = constraint.actual.clone();
                add_hole_and_t(hole, t, constraint.actual_origin);
            }
            (_t, Type::Unknown(_)) => {
                let hole = constraint.actual.clone();
                let t = constraint.expected.clone();
                add_hole_and_t(hole, t, constraint.expected_origin);
            }
            (Type::Arrow(left1, right1), Type::Arrow(left2, right2)) => {
                constraints.push(Constraint {
                    expected: left1.clone(),
                    expected_origin: None,
                    actual: left2.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: right1.clone(),
                    expected_origin: None,
                    actual: right2.clone(),
                    actual_origin: None,
                });
            }
            _ => {}
        }
    }

    let mut unsolved_type_suggestions_to_unknown_ty = MultiMap::new();
    for (unknown_ty, potential_types) in &unknown_ty_to_potential_types {
        let type_suggestions = condense_candidates(potential_types);
        if type_suggestions.unsolved() {
            unsolved_type_suggestions_to_unknown_ty.insert(type_suggestions, unknown_ty);
        }
    }

    if unsolved_type_suggestions_to_unknown_ty.is_empty() {
        return Ok(());
    }

    let mut err_string = String::new();
    err_string.push_str("You have a type error!\n");

    for (type_conflict, _unknown_tys) in unsolved_type_suggestions_to_unknown_ty {
        err_string.push_str(&format!("Type Conflict: {}\n", type_conflict));
        err_string.push_str("Sources of ");
        for ty in type_conflict.types {
            match &ty {
                TypeSuggestion::Unit(causes)
                | TypeSuggestion::Int(causes)
                | TypeSuggestion::Bool(causes)
                | TypeSuggestion::String(causes) => {
                    match &ty {
                        TypeSuggestion::Unit(_) => err_string.push_str("unit:\n"),
                        TypeSuggestion::Int(_) => err_string.push_str("int:\n"),
                        TypeSuggestion::Bool(_) => err_string.push_str("bool:\n"),
                        TypeSuggestion::String(_) => err_string.push_str("string:\n"),
                        _ => unreachable!(),
                    };
                    for cause in causes {
                        let span = node_map.get(cause).unwrap().span();
                        err_string.push_str(&span.display(source, ""));
                    }
                }
                _ => (),
            }
        }
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
    Ana {
        expected: Rc<Type>,
        expected_origin: Option<ast::Id>,
    },
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
            Mode::Ana {
                expected,
                expected_origin,
            } => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: Rc::new(Type::Unit),
                    actual_origin: Some(expr.id.clone()),
                });
            }
        },
        ExprKind::Int(_) => match mode {
            Mode::Syn => (),
            Mode::Ana {
                expected,
                expected_origin,
            } => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: Rc::new(Type::Int),
                    actual_origin: Some(expr.id.clone()),
                });
            }
        },
        ExprKind::Bool(_) => match mode {
            Mode::Syn => (),
            Mode::Ana {
                expected,
                expected_origin,
            } => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: Rc::new(Type::Bool),
                    actual_origin: Some(expr.id.clone()),
                });
            }
        },
        ExprKind::Str(_) => match mode {
            Mode::Syn => (),
            Mode::Ana {
                expected,
                expected_origin,
            } => {
                let node_ty = Rc::new(Type::Unknown(Prov::Node(expr.id.clone())));
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: Rc::new(Type::String),
                    actual_origin: Some(expr.id.clone()),
                });
            }
        },
        ExprKind::Var(id) => {
            let lookup = ctx.borrow_mut().lookup(id);
            match lookup {
                Some(typ) => match mode {
                    Mode::Syn => (),
                    Mode::Ana {
                        expected,
                        expected_origin,
                    } => constraints.push(Constraint {
                        expected,
                        expected_origin,
                        actual: typ,
                        actual_origin: Some(expr.id.clone()),
                    }),
                },
                None => match mode {
                    Mode::Syn => (),
                    Mode::Ana {
                        expected,
                        expected_origin,
                    } => constraints.push(Constraint {
                        expected,
                        expected_origin,
                        actual: Type::Unknown(Prov::Node(expr.id.clone())).into(),
                        actual_origin: None,
                    }),
                },
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op);
            match mode {
                Mode::Syn => (),
                Mode::Ana {
                    expected,
                    expected_origin,
                } => {
                    constraints.push(Constraint {
                        expected,
                        expected_origin,
                        actual: ty_out,
                        actual_origin: Some(expr.id.clone()),
                    });
                }
            };
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: ty_left,
                    expected_origin: Some(expr.id.clone()),
                },
                left.clone(),
                constraints,
            );
            generate_constraints_expr(
                ctx,
                Mode::Ana {
                    expected: ty_right,
                    expected_origin: Some(expr.id.clone()),
                },
                right.clone(),
                constraints,
            );
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
                    Mode::Ana {
                        expected,
                        expected_origin,
                    } => constraints.push(Constraint {
                        expected,
                        expected_origin,
                        actual: Rc::new(Type::Unit),
                        actual_origin: Some(expr.id.clone()),
                    }),
                },
            };
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: Rc::new(Type::Bool),
                    expected_origin: Some(cond.id.clone()),
                },
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
                Mode::Ana {
                    expected: ty_body.clone(),
                    expected_origin: None,
                },
                body.clone(),
                constraints,
            );

            let ty_func = Type::make_arrow(ty_args, ty_body);
            match mode {
                Mode::Syn => (),
                Mode::Ana {
                    expected,
                    expected_origin,
                } => constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: ty_func,
                    actual_origin: None,
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
                        Mode::Ana {
                            expected: unknown.clone(),
                            expected_origin: None,
                        },
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
            generate_constraints_expr(
                ctx,
                Mode::Ana {
                    expected: ty_func,
                    expected_origin: None,
                },
                func.clone(),
                constraints,
            );
            match mode {
                Mode::Syn => (),
                Mode::Ana {
                    expected,
                    expected_origin,
                } => constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: ty_body,
                    actual_origin: None,
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
                Mode::Ana {
                    expected: ty_pat,
                    expected_origin: None,
                },
                expr.clone(),
                constraints,
            );
            Some(new_ctx)
        }
    }
}
