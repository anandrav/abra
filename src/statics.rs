use crate::ast::{self, *};
use crate::types::{types_of_binop, Prov, SType, STypeKind};
use disjoint_sets::UnionFindNode;
use multimap::MultiMap;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Write};
use std::rc::Rc;

#[derive(Debug)]
pub struct Constraint {
    expected: Rc<SType>,
    actual: Rc<SType>,
}

type UFPotentialTypes = UnionFindNode<UFPotentialTypes_>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum PotentialTypeCtor {
    Unit,
    Int,
    Bool,
    String,
    Arrow(u8),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UFPotentialType {
    // TODO: don't store Ctor in Primitive/Binary, it's already the key of the map.
    Primitive(PotentialTypeCtor, Provs),
    Nary(
        PotentialTypeCtor,
        Provs,
        Vec<UFPotentialTypes>,
        UFPotentialTypes,
    ),
}

impl UFPotentialType {
    pub fn provs(&self) -> &Provs {
        match &self {
            Self::Primitive(_, provs) => provs,
            Self::Nary(_, provs, _, _) => provs,
        }
    }

    pub fn provs_mut(&mut self) -> &mut Provs {
        match self {
            Self::Primitive(_, provs) => provs,
            Self::Nary(_, provs, _, _) => provs,
        }
    }
}

pub type Provs = BTreeSet<Prov>;

// creates a UFTypeCandidates from the unknown type
// only adds/retrieves from the graph if the type is holey!
fn retrieve_and_or_add_node(
    unknown_ty_to_potential_types: &mut HashMap<Prov, UFPotentialTypes>,
    unknown: Rc<SType>,
    _: Option<Prov>,
) -> UFPotentialTypes {
    let provs_single = {
        let mut set = BTreeSet::new();
        set.insert(unknown.prov.clone());
        set
    };
    match &unknown.typekind {
        STypeKind::Unknown => {
            let prov = &unknown.prov;
            if let Some(node) = unknown_ty_to_potential_types.get(prov) {
                node.clone()
            } else {
                let node = UnionFindNode::new(UFPotentialTypes_::empty());
                unknown_ty_to_potential_types.insert(prov.clone(), node.clone());
                node
            }
        }
        STypeKind::Arrow(args, out) => {
            let args: Vec<_> = args
                .iter()
                .map(|arg| {
                    retrieve_and_or_add_node(unknown_ty_to_potential_types, arg.clone(), None)
                })
                .collect();
            let out = retrieve_and_or_add_node(unknown_ty_to_potential_types, out.clone(), None);
            UnionFindNode::new(UFPotentialTypes_::singleton(
                PotentialTypeCtor::Arrow(args.len() as u8),
                UFPotentialType::Nary(
                    PotentialTypeCtor::Arrow(args.len() as u8),
                    provs_single,
                    args,
                    out,
                ),
            ))
        }
        STypeKind::Unit => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Unit,
            UFPotentialType::Primitive(PotentialTypeCtor::Unit, provs_single),
        )),
        STypeKind::Int => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Int,
            UFPotentialType::Primitive(PotentialTypeCtor::Int, provs_single),
        )),
        STypeKind::Bool => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::Bool,
            UFPotentialType::Primitive(PotentialTypeCtor::Bool, provs_single),
        )),
        STypeKind::String => UnionFindNode::new(UFPotentialTypes_::singleton(
            PotentialTypeCtor::String,
            UFPotentialType::Primitive(PotentialTypeCtor::String, provs_single),
        )),
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TypeSuggestion {
    Unknown,
    Unit(Provs),
    Int(Provs),
    Bool(Provs),
    String(Provs),
    Arrow(Provs, Vec<TypeSuggestions>, TypeSuggestions),
}

impl fmt::Display for TypeSuggestion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TypeSuggestion::Unknown => write!(f, "?"),
            TypeSuggestion::Unit(_) => write!(f, "void"),
            TypeSuggestion::Int(_) => write!(f, "int"),
            TypeSuggestion::Bool(_) => write!(f, "bool"),
            TypeSuggestion::String(_) => write!(f, "string"),
            TypeSuggestion::Arrow(_, args, out) => {
                if args.len() > 1 {
                    write!(f, "(")?;
                }
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    if arg.types.len() > 1 {
                        write!(f, "?")?;
                    } else {
                        write!(f, "{}", arg.types.first().unwrap())?;
                    }
                }
                if args.len() > 1 {
                    write!(f, ")")?;
                }
                write!(f, " -> ")?;
                if out.types.len() > 1 {
                    write!(f, "?")
                } else {
                    write!(f, "{}", out.types.first().unwrap())
                }
            }
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

fn fmt_type_suggestions(types: &Vec<&TypeSuggestion>, f: &mut dyn Write) -> fmt::Result {
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

pub fn condense_candidates(uf_type_candidates: &UFPotentialTypes) -> TypeSuggestions {
    let condensed = uf_type_candidates.clone_data();
    let mut types: BTreeSet<TypeSuggestion> = BTreeSet::new();
    for (ctor, potential_type) in &condensed.types {
        match (ctor, potential_type) {
            (PotentialTypeCtor::Unit, _) => {
                let t = TypeSuggestion::Unit(potential_type.provs().clone());
                types.insert(t);
            }
            (PotentialTypeCtor::Int, _) => {
                let t = TypeSuggestion::Int(potential_type.provs().clone());
                types.insert(t);
            }
            (PotentialTypeCtor::Bool, _) => {
                let t = TypeSuggestion::Bool(potential_type.provs().clone());
                types.insert(t);
            }
            (PotentialTypeCtor::String, _) => {
                let t = TypeSuggestion::String(potential_type.provs().clone());
                types.insert(t);
            }
            (
                PotentialTypeCtor::Arrow(_),
                UFPotentialType::Nary(PotentialTypeCtor::Arrow(_), provs, args, out),
            ) => {
                let args: Vec<_> = args.iter().map(condense_candidates).collect();
                let out = condense_candidates(out);
                types.insert(TypeSuggestion::Arrow(provs.clone(), args, out));
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
                UFPotentialType::Primitive(_, other_provs) => {
                    t.provs_mut().extend(other_provs);
                }
                UFPotentialType::Nary(
                    PotentialTypeCtor::Arrow(_),
                    other_provs,
                    ref mut args_other,
                    ref mut out_other,
                ) => match &mut t {
                    UFPotentialType::Nary(
                        PotentialTypeCtor::Arrow(_),
                        t_provs,
                        ref mut args,
                        ref mut out,
                    ) => {
                        if args.len() != args_other.len() {
                            panic!("should be same arity");
                        }
                        t_provs.extend(other_provs);
                        for i in 0..args.len() {
                            let (t_arg, other_arg) = (&mut args[i], &mut args_other[i]);
                            t_arg.union_with(other_arg, UFPotentialTypes_::merge);
                        }
                        out.union_with(out_other, UFPotentialTypes_::merge);
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

    let mut add_hole_and_t = |hole: Rc<SType>, t: Rc<SType>, cause: Prov| {
        let mut hole_node =
            retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, hole, None);
        let mut t_node =
            retrieve_and_or_add_node(&mut unknown_ty_to_potential_types, t, Some(cause));
        hole_node.union_with(&mut t_node, UFPotentialTypes_::merge);
    };
    while !constraints.is_empty() {
        let constraint = constraints.pop().unwrap();
        match (&constraint.expected.typekind, &constraint.actual.typekind) {
            (STypeKind::Unknown, _t) => {
                let hole = constraint.expected.clone();
                let t = constraint.actual.clone();
                add_hole_and_t(hole, t, constraint.actual.prov.clone());
            }
            (_t, STypeKind::Unknown) => {
                let hole = constraint.actual.clone();
                let t = constraint.expected.clone();
                add_hole_and_t(hole, t, constraint.expected.prov.clone());
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

    let mut type_conflicts = unsolved_type_suggestions_to_unknown_ty
        .keys()
        .map(|type_suggestions| {
            let mut types_sorted: Vec<_> = type_suggestions.types.iter().collect();
            types_sorted.sort_by_key(|ty| match ty {
                TypeSuggestion::Unknown => unreachable!(),
                TypeSuggestion::Unit(provs)
                | TypeSuggestion::Int(provs)
                | TypeSuggestion::Bool(provs)
                | TypeSuggestion::String(provs)
                | TypeSuggestion::Arrow(provs, _, _) => provs.len(),
            });
            types_sorted
        })
        .collect::<Vec<_>>();
    type_conflicts.sort();
    for type_conflict in type_conflicts {
        err_string.push_str("Type Conflict: ");
        fmt_type_suggestions(&type_conflict, &mut err_string).unwrap();
        writeln!(err_string).unwrap();
        for ty in type_conflict {
            err_string.push('\n');
            match &ty {
                TypeSuggestion::Unknown => unreachable!(),
                TypeSuggestion::Unit(_) => err_string.push_str("Sources of unit:\n"),
                TypeSuggestion::Int(_) => err_string.push_str("Sources of int:\n"),
                TypeSuggestion::Bool(_) => err_string.push_str("Sources of bool:\n"),
                TypeSuggestion::String(_) => err_string.push_str("Sources of string:\n"),
                TypeSuggestion::Arrow(_, args, _) => err_string.push_str(&format!(
                    "Sources of function with {} arguments:\n",
                    args.len()
                )),
            };
            let provs = match &ty {
                TypeSuggestion::Unknown => unreachable!(),
                TypeSuggestion::Unit(provs)
                | TypeSuggestion::Int(provs)
                | TypeSuggestion::Bool(provs)
                | TypeSuggestion::String(provs)
                | TypeSuggestion::Arrow(provs, _, _) => provs,
            };
            for cause in provs {
                match cause {
                    Prov::Builtin(s) => {
                        err_string.push_str(&format!("The builtin function '{}'", s));
                    }
                    Prov::Node(id) => {
                        let span = node_map.get(id).unwrap().span();
                        err_string.push_str(&span.display(source, ""));
                    }
                    Prov::FuncArg(prov, n) => {
                        match prov.as_ref() {
                            Prov::Builtin(s) => {
                                let n = n + 1; // readability
                                err_string.push_str(&format!(
                                    "--> The #{n} argument of the builtin function '{}'\n",
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
                }
            }
        }
        writeln!(err_string).unwrap();
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
                vec![SType::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin("print".to_string())),
                    0,
                ))],
                SType::make_unit(Prov::FuncArg(
                    Box::new(Prov::Builtin("print".to_string())),
                    1,
                )),
            ),
            prov: Prov::Builtin("print".to_string()),
        }),
    );
    ctx.borrow_mut().extend(
        &String::from("string_of_int"),
        Rc::new(SType {
            typekind: STypeKind::Arrow(
                vec![SType::make_int(Prov::FuncArg(
                    Box::new(Prov::Builtin("string_of_int".to_string())),
                    0,
                ))],
                SType::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin("string_of_int".to_string())),
                    1,
                )),
            ),
            prov: Prov::Builtin("string_of_int".to_string()),
        }),
    );
    ctx
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
    Ana { expected: Rc<SType> },
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
            Mode::Ana { expected } => {
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: SType::make_unit(Prov::Node(expr.id)),
                });
            }
        },
        ExprKind::Int(_) => match mode {
            Mode::Syn => (),
            Mode::Ana { expected } => {
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: SType::make_int(Prov::Node(expr.id)),
                });
            }
        },
        ExprKind::Bool(_) => match mode {
            Mode::Syn => (),
            Mode::Ana { expected } => {
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: SType::make_bool(Prov::Node(expr.id)),
                });
            }
        },
        ExprKind::Str(_) => match mode {
            Mode::Syn => (),
            Mode::Ana { expected } => {
                let node_ty = SType::from_node(expr.clone());
                constraints.push(Constraint {
                    expected,
                    actual: node_ty.clone(),
                });
                constraints.push(Constraint {
                    expected: node_ty,
                    actual: SType::make_string(Prov::Node(expr.id)),
                });
            }
        },
        ExprKind::Var(id) => {
            let lookup = ctx.borrow_mut().lookup(id);
            match lookup {
                Some(typ) => match mode {
                    Mode::Syn => (),
                    Mode::Ana { expected } => constraints.push(Constraint {
                        expected,
                        actual: typ,
                    }),
                },
                None => match mode {
                    Mode::Syn => (),
                    Mode::Ana { expected } => constraints.push(Constraint {
                        expected,
                        actual: SType::from_node(expr.clone()),
                    }),
                },
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) =
                types_of_binop(op, left.clone(), right.clone(), expr.clone());
            match mode {
                Mode::Syn => (),
                Mode::Ana { expected } => {
                    constraints.push(Constraint {
                        expected,
                        actual: ty_out,
                    });
                }
            };
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana { expected: ty_left },
                left.clone(),
                constraints,
            );
            generate_constraints_expr(
                ctx,
                Mode::Ana { expected: ty_right },
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
                    Mode::Ana { expected } => constraints.push(Constraint {
                        expected,
                        actual: SType::make_unit(Prov::Node(expr.id)),
                    }),
                },
            };
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: SType::make_bool(Prov::Node(cond.id)),
                },
                cond.clone(),
                constraints,
            );
            generate_constraints_expr(ctx.clone(), mode.clone(), expr1.clone(), constraints);
            generate_constraints_expr(ctx, mode, expr2.clone(), constraints);
        }
        ExprKind::Func(args, out_annot, body) => {
            let mut new_ctx = TyCtx::new(Some(ctx));

            let ty_args = args
                .iter()
                .map(|(arg, arg_annot)| {
                    let ty_pat = SType::from_node(arg.clone());
                    new_ctx = if let Some(arg_annot) = arg_annot {
                        generate_constraints_pat(
                            new_ctx.clone(), // TODO what are the consequences of analyzing patterns with context containing previous pattern... probs should not do that
                            Mode::Ana {
                                expected: ast_type_to_statics_type(arg_annot.clone()),
                            },
                            arg.clone(),
                            constraints,
                        )
                    } else {
                        generate_constraints_pat(
                            new_ctx.clone(),
                            Mode::Syn,
                            arg.clone(),
                            constraints,
                        )
                    }
                    .unwrap_or(new_ctx.clone());
                    ty_pat
                })
                .collect();

            let ty_body = SType::make_unknown(Prov::FuncOut(Box::new(Prov::Node(expr.id))));
            generate_constraints_expr(
                new_ctx.clone(),
                Mode::Ana {
                    expected: ty_body.clone(),
                },
                body.clone(),
                constraints,
            );
            if let Some(out_annot) = out_annot {
                generate_constraints_expr(
                    new_ctx,
                    Mode::Ana {
                        expected: ast_type_to_statics_type(out_annot.clone()),
                    },
                    body.clone(),
                    constraints,
                );
            }

            let ty_func = SType::make_arrow(ty_args, ty_body, expr.id);
            match mode {
                Mode::Syn => (),
                Mode::Ana { expected } => constraints.push(Constraint {
                    expected,
                    actual: ty_func,
                }),
            };
        }
        ExprKind::FuncAp(func, args) => {
            let tys_args: Vec<Rc<SType>> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown =
                        SType::make_unknown(Prov::FuncArg(Box::new(Prov::Node(func.id)), n as u8));
                    generate_constraints_expr(
                        ctx.clone(),
                        Mode::Ana {
                            expected: unknown.clone(),
                        },
                        arg.clone(),
                        constraints,
                    );
                    unknown
                })
                .collect();

            let ty_body = SType::make_unknown(Prov::FuncOut(Box::new(Prov::Node(func.id))));

            let ty_func = SType::make_arrow(tys_args, ty_body.clone(), expr.id);
            generate_constraints_expr(
                ctx,
                Mode::Ana { expected: ty_func },
                func.clone(),
                constraints,
            );
            match mode {
                Mode::Syn => (),
                Mode::Ana { expected } => constraints.push(Constraint {
                    expected,
                    actual: ty_body,
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
            let ty_annotation = ty_opt
                .as_ref()
                .map(|ty| ast_type_to_statics_type(ty.clone()));

            let new_ctx = if let Some(ty_annotation) = ty_annotation {
                generate_constraints_pat(
                    ctx.clone(),
                    Mode::Ana {
                        expected: ty_annotation,
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
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                constraints,
            );
            Some(ctx)
        }
    }
}

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
                Mode::Ana { expected } => constraints.push(Constraint {
                    expected,
                    actual: ty_pat,
                }),
            };
            Some(new_ctx)
        }
    }
}
