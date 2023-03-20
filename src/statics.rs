use crate::ast::{self, *};
use crate::types::{types_of_binop, Prov, SType, STypeKind};
use disjoint_sets::UnionFindNode;
use multimap::MultiMap;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self};
use std::rc::Rc;

#[derive(Debug)]
pub struct Constraint {
    expected: Rc<SType>,
    // TODO: it might be better for origin to go in the type itself. There is overlap between Unknown provenances and Known type origins...
    expected_origin: Option<ast::Id>,
    actual: Rc<SType>,
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
    Primitive(PotentialTypeCtor, Origins),
    Binary(
        PotentialTypeCtor,
        Origins,
        UFPotentialTypes,
        UFPotentialTypes,
    ),
}

impl UFPotentialType {
    pub fn causes(&self) -> &Origins {
        match &self {
            Self::Primitive(_, causes) => causes,
            Self::Binary(_, causes, _, _) => causes,
        }
    }

    pub fn causes_mut(&mut self) -> &mut Origins {
        match self {
            Self::Primitive(_, causes) => causes,
            Self::Binary(_, causes, _, _) => causes,
        }
    }
}

pub type Origins = BTreeSet<ast::Id>;

// creates a UFTypeCandidates from the unknown type
// only adds/retrieves from the graph if the type is holey!
fn retrieve_and_or_add_node(
    unknown_ty_to_candidates: &mut HashMap<Prov, UFPotentialTypes>,
    unknown: Rc<SType>,
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
    match &unknown.typekind {
        STypeKind::Unknown => {
            let prov = &unknown.prov;
            if let Some(node) = unknown_ty_to_candidates.get(&prov) {
                node.clone()
            } else {
                let node = UnionFindNode::new(UFPotentialTypes_::empty());
                unknown_ty_to_candidates.insert(prov.clone(), node.clone());
                node
            }
        }
        STypeKind::Arrow(t1, t2) => {
            let t1 = retrieve_and_or_add_node(unknown_ty_to_candidates, t1.clone(), None);
            let t2 = retrieve_and_or_add_node(unknown_ty_to_candidates, t2.clone(), None);
            UnionFindNode::new(UFPotentialTypes_::singleton(
                PotentialTypeCtor::Arrow,
                UFPotentialType::Binary(PotentialTypeCtor::Arrow, causes_single, t1, t2),
            ))
        }
        STypeKind::Unit => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Unit,
            UFPotentialType::Primitive(PotentialTypeCtor::Unit, causes_single),
        )),
        STypeKind::Int => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Int,
            UFPotentialType::Primitive(PotentialTypeCtor::Int, causes_single),
        )),
        STypeKind::Bool => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Bool,
            UFPotentialType::Primitive(PotentialTypeCtor::Bool, causes_single),
        )),
        STypeKind::String => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::String,
            UFPotentialType::Primitive(PotentialTypeCtor::String, causes_single),
        )),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSuggestion {
    Unknown,
    Unit(Origins),
    Int(Origins),
    Bool(Origins),
    String(Origins),
    Arrow(Origins, TypeSuggestions, TypeSuggestions),
}

impl fmt::Display for TypeSuggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeSuggestion::Unknown => write!(f, "?"),
            TypeSuggestion::Unit(_) => write!(f, "unit"),
            TypeSuggestion::Int(_) => write!(f, "int"),
            TypeSuggestion::Bool(_) => write!(f, "bool"),
            TypeSuggestion::String(_) => write!(f, "string"),
            TypeSuggestion::Arrow(_, t1, t2) => write!(f, "({} -> {})", t1, t2),
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
                UFPotentialType::Binary(PotentialTypeCtor::Arrow, causes, t1, t2),
            ) => {
                let t1 = condense_candidates(t1);
                let t2 = condense_candidates(t2);
                types.insert(TypeSuggestion::Arrow(causes.clone(), t1, t2));
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

    // TODO: occurs check
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

    // TODO: occurs check
    fn merge(first: Self, second: Self) -> Self {
        let mut merged_types = Self { types: first.types };
        for (ctor, t) in second.types {
            merged_types.extend(ctor, t);
        }
        merged_types
    }
}

// TODO: since each expr/pattern node has a type, the node map should be populated with the types (and errors) of each node. So node id -> {Rc<Node>, StaticsSummary}
// errors would be unbound variable, wrong number of arguments, occurs check, etc.
pub fn solve_constraints(
    constraints: Vec<Constraint>,
    node_map: ast::NodeMap,
    source: &str,
) -> Result<(), String> {
    let mut constraints = constraints;
    // this is the graph, which only contains unknown types or types containing unknown types. Make a new struct for it later.
    let mut unknown_ty_to_potential_types: HashMap<Prov, UFPotentialTypes> = HashMap::new();

    let mut add_hole_and_t = |hole: Rc<SType>, t: Rc<SType>, cause: Option<ast::Id>| {
        let mut hole_node =
            retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, hole, None);
        let mut t_node = retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, t, cause);
        hole_node.union_with(&mut t_node, UFPotentialTypes_::merge);
    };
    while !constraints.is_empty() {
        let constraint = constraints.pop().unwrap();
        match (&constraint.expected.typekind, &constraint.actual.typekind) {
            (STypeKind::Unknown, _t) => {
                let hole = constraint.expected.clone();
                let t = constraint.actual.clone();
                add_hole_and_t(hole, t, constraint.actual_origin);
            }
            (_t, STypeKind::Unknown) => {
                let hole = constraint.actual.clone();
                let t = constraint.expected.clone();
                add_hole_and_t(hole, t, constraint.expected_origin);
            }
            (STypeKind::Arrow(left1, right1), STypeKind::Arrow(left2, right2)) => {
                constraints.push(Constraint {
                    expected: left1.clone(),
                    expected_origin: constraint.expected_origin.clone(),
                    actual: left2.clone(),
                    actual_origin: constraint.actual_origin.clone(),
                });
                constraints.push(Constraint {
                    expected: right1.clone(),
                    expected_origin: constraint.expected_origin,
                    actual: right2.clone(),
                    actual_origin: constraint.actual_origin,
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
                TypeSuggestion::Unknown => unreachable!(),
                TypeSuggestion::Unit(_) => err_string.push_str("unit:\n"),
                TypeSuggestion::Int(_) => err_string.push_str("int:\n"),
                TypeSuggestion::Bool(_) => err_string.push_str("bool:\n"),
                TypeSuggestion::String(_) => err_string.push_str("string:\n"),
                TypeSuggestion::Arrow(_, _, _) => err_string.push_str("function:\n"),
            };
            let causes = match &ty {
                TypeSuggestion::Unknown => unreachable!(),
                TypeSuggestion::Unit(causes)
                | TypeSuggestion::Int(causes)
                | TypeSuggestion::Bool(causes)
                | TypeSuggestion::String(causes)
                | TypeSuggestion::Arrow(causes, _, _) => causes,
            };
            for cause in causes {
                let span = node_map.get(cause).unwrap().span();
                err_string.push_str(&span.display(source, ""));
            }
        }
    }

    Err(err_string)
}

pub struct TyCtx {
    vars: HashMap<Identifier, Rc<SType>>,
    enclosing: Option<Rc<RefCell<TyCtx>>>,
}

pub fn make_new_environment() -> Rc<RefCell<TyCtx>> {
    let ctx = TyCtx::empty();
    ctx.borrow_mut().extend(
        &String::from("print"),
        Rc::new(SType {
            typekind: STypeKind::Arrow(
                SType::make_string(Prov::Builtin),
                SType::make_unit(Prov::Builtin),
            ),
            prov: Prov::Builtin,
        }),
    );
    ctx.borrow_mut().extend(
        &String::from("string_of_int"),
        Rc::new(SType {
            typekind: STypeKind::Arrow(
                SType::make_int(Prov::Builtin),
                SType::make_string(Prov::Builtin),
            ),
            prov: Prov::Builtin,
        }),
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

    pub fn lookup(&self, id: &Identifier) -> Option<Rc<SType>> {
        match self.vars.get(id) {
            Some(typ) => Some(typ.clone()),
            None => match &self.enclosing {
                Some(env) => env.borrow_mut().lookup(id),
                None => None,
            },
        }
    }

    pub fn extend(&mut self, id: &Identifier, typ: Rc<SType>) {
        self.vars.insert(id.clone(), typ);
    }
}

#[derive(Debug, Clone)]
pub enum Mode {
    Syn,
    Ana {
        expected: Rc<SType>,
        expected_origin: Option<ast::Id>,
    },
}

pub fn generate_constraints_expr(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    expr: Rc<Expr>,
    constraints: &mut Vec<Constraint>,
) {
    match &*expr.exprkind {
        ExprKind::Unit => match mode {
            Mode::Syn => (),
            Mode::Ana {
                expected,
                expected_origin,
            } => {
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: SType::make_unit(Prov::Node(expr.id.clone())),
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
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: SType::make_int(Prov::Node(expr.id.clone())),
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
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: SType::make_bool(Prov::Node(expr.id.clone())),
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
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: node_ty.clone(),
                    actual_origin: None,
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    expected_origin: None,
                    actual: SType::make_string(Prov::Node(expr.id.clone())),
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
                        actual: SType::from_node(expr.clone()),
                        actual_origin: None,
                    }),
                },
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) =
                types_of_binop(op, left.clone(), right.clone(), expr.clone());
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
                        actual: SType::make_unit(Prov::Node(expr.id.clone())),
                        actual_origin: Some(expr.id.clone()),
                    }),
                },
            };
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: SType::make_bool(Prov::Node(cond.id.clone())), // TODO: Prov should mention it's the condition of an if
                    expected_origin: Some(cond.id.clone()),
                },
                cond.clone(),
                constraints,
            );
            generate_constraints_expr(ctx.clone(), mode.clone(), expr1.clone(), constraints);
            generate_constraints_expr(ctx, mode, expr2.clone(), constraints);
        }
        ExprKind::Func(args, _, body) => {
            let mut new_ctx = TyCtx::new(Some(ctx.clone()));

            let ty_args = args
                .iter()
                .map(|(arg, ty_opt)| {
                    let ty_pat = SType::from_node(arg.clone());
                    new_ctx = if let Some(ty_annotation) = ty_opt {
                        generate_constraints_pat(
                            ctx.clone(),
                            Mode::Ana {
                                expected: ast_type_to_statics_type(ty_annotation.clone()),
                                expected_origin: Some(ty_annotation.id()),
                            },
                            arg.clone(),
                            constraints,
                        )
                    } else {
                        generate_constraints_pat(ctx.clone(), Mode::Syn, arg.clone(), constraints)
                    }
                    .unwrap_or(new_ctx.clone());
                    ty_pat
                })
                .collect();

            let ty_body = SType::from_node(body.clone());
            generate_constraints_expr(
                new_ctx,
                Mode::Ana {
                    expected: ty_body.clone(),
                    expected_origin: Some(expr.id.clone()),
                },
                body.clone(),
                constraints,
            );

            let ty_func = SType::make_arrow(ty_args, ty_body, expr.id);
            match mode {
                Mode::Syn => (),
                Mode::Ana {
                    expected,
                    expected_origin,
                } => constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: ty_func,
                    actual_origin: Some(expr.id.clone()),
                }),
            };
        }
        ExprKind::FuncAp(func, args) => {
            let tys_args: Vec<Rc<SType>> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = SType::make_unknown(Prov::FuncArg(func.id.clone(), n as u8));
                    generate_constraints_expr(
                        ctx.clone(),
                        Mode::Ana {
                            expected: unknown.clone(),
                            expected_origin: Some(expr.id.clone()), // TODO origin needs more detail like provenances... nth arg of func application
                        },
                        arg.clone(),
                        constraints,
                    );
                    unknown
                })
                .collect();

            let ty_body = SType::make_unknown(Prov::FuncOut(func.id.clone(), tys_args.len() as u8));

            let ty_func = SType::make_arrow(tys_args, ty_body.clone(), expr.id);
            generate_constraints_expr(
                ctx,
                Mode::Ana {
                    expected: ty_func,
                    expected_origin: Some(expr.id.clone()),
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
                    actual_origin: Some(expr.id.clone()),
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
        StmtKind::Let((pat, ty_opt), expr) => {
            let ty_pat = SType::from_node(pat.clone());
            // TODO don't use ast_type_to_boring_type
            let ty_annotation = ty_opt
                .as_ref()
                .map(|ty| (ast_type_to_statics_type(ty.clone()), ty.id()));

            let new_ctx = if let Some((ty_annotation, id)) = ty_annotation {
                generate_constraints_pat(
                    ctx.clone(),
                    Mode::Ana {
                        expected: ty_annotation,
                        expected_origin: Some(id),
                    },
                    pat.clone(),
                    constraints,
                )
            } else {
                generate_constraints_pat(ctx.clone(), Mode::Syn, pat.clone(), constraints)
            };

            let ctx = new_ctx.unwrap_or(ctx);
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: ty_pat,
                    expected_origin: None,
                },
                expr.clone(),
                constraints,
            );
            Some(ctx)
        }
    }
}

// TODO extend ctx with identifier in here, not up there
pub fn generate_constraints_pat(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    pat: Rc<Pat>,
    constraints: &mut Vec<Constraint>,
) -> Option<Rc<RefCell<TyCtx>>> {
    let new_ctx = TyCtx::new(Some(ctx));
    match &*pat.patkind {
        PatKind::Var(identifier) => {
            // letrec?: extend context with id and type before analyzing against said type
            let ty_pat = SType::from_node(pat.clone());
            new_ctx.borrow_mut().extend(identifier, ty_pat.clone());
            match mode {
                Mode::Syn => (),
                Mode::Ana {
                    expected,
                    expected_origin,
                } => constraints.push(Constraint {
                    expected,
                    expected_origin,
                    actual: ty_pat,
                    actual_origin: Some(pat.id.clone()),
                }),
            };
            Some(new_ctx)
        }
    }
}
