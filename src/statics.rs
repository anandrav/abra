use crate::ast::{self, *};
use crate::types::{types_of_binop, Prov, SType, STypeKind};
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::fmt::{self, Write};
use std::rc::Rc;

#[derive(Debug)]
pub struct Constraint {
    expected: Rc<SType>,
    actual: Rc<SType>,
}

type UFTypeVar = UnionFindNode<UFTypeVar_>;

fn fmt_uftype_var(tvar: &UFTypeVar, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut result = Ok(());
    tvar.with_data(|tvar_| {
        result = if tvar_.types.is_empty() {
            write!(f, "'?")
        } else if tvar_.types.len() == 1 {
            write!(f, "{}", tvar_.types.iter().next().unwrap().1)
        } else {
            write!(f, "'?")
        }
    });
    result
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum TypeCtor {
    Unit,
    Int,
    Bool,
    String,
    Arrow(u8),
    Tuple(u8),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum UFType {
    Unit(Provs),
    Int(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<UFTypeVar>, UFTypeVar),
    Tuple(Provs, Vec<UFTypeVar>), // TODO remove this ctor if you can
}

impl fmt::Display for UFType {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            UFType::Unit(_) => write!(f, "void"),
            UFType::Int(_) => write!(f, "int"),
            UFType::Bool(_) => write!(f, "bool"),
            UFType::String(_) => write!(f, "string"),
            UFType::Function(_, args, out) => {
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    fmt_uftype_var(arg, f)?;
                }
                write!(f, " -> ")?;
                fmt_uftype_var(out, f)
            }
            UFType::Tuple(_, elems) => {
                write!(f, "(")?;
                for (i, elem) in elems.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "{:#?}", elem)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl UFType {
    pub fn provs(&self) -> &Provs {
        match self {
            Self::Unit(provs)
            | Self::Int(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _) => provs,
        }
    }

    pub fn provs_mut(&mut self) -> &mut Provs {
        match self {
            Self::Unit(provs)
            | Self::Int(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _) => provs,
        }
    }
}

pub type Provs = BTreeSet<Prov>;

pub type SolutionMap = HashMap<Prov, UFTypeVar>;
trait SolutionMapTrait {
    fn add_constraint(&mut self, constraint: Constraint);

    fn retrieve_and_or_add_node(&mut self, unknown: Rc<SType>) -> UFTypeVar;
}

impl SolutionMapTrait for SolutionMap {
    fn retrieve_and_or_add_node(&mut self, unknown: Rc<SType>) -> UFTypeVar {
        let provs_single = {
            let mut set = BTreeSet::new();
            set.insert(unknown.prov.clone());
            set
        };
        match &unknown.typekind {
            STypeKind::Unknown => {
                let prov = &unknown.prov;
                if let Some(node) = self.get(prov) {
                    node.clone()
                } else {
                    let node = UnionFindNode::new(UFTypeVar_::empty());
                    self.insert(prov.clone(), node.clone());
                    node
                }
            }
            STypeKind::Arrow(args, out) => {
                let args: Vec<_> = args
                    .iter()
                    .map(|arg| self.retrieve_and_or_add_node(arg.clone()))
                    .collect();
                let out = self.retrieve_and_or_add_node(out.clone());
                UnionFindNode::new(UFTypeVar_::singleton(
                    TypeCtor::Arrow(args.len() as u8),
                    UFType::Function(provs_single, args, out),
                ))
            }
            STypeKind::Tuple(exprs) => {
                let exprs: Vec<_> = exprs
                    .iter()
                    .map(|expr| self.retrieve_and_or_add_node(expr.clone()))
                    .collect();
                UnionFindNode::new(UFTypeVar_::singleton(
                    TypeCtor::Tuple(exprs.len() as u8),
                    UFType::Tuple(provs_single, exprs),
                ))
            }
            STypeKind::Unit => UnionFindNode::new(UFTypeVar_::singleton(
                TypeCtor::Unit,
                UFType::Unit(provs_single),
            )),
            STypeKind::Int => UnionFindNode::new(UFTypeVar_::singleton(
                TypeCtor::Int,
                UFType::Int(provs_single),
            )),
            STypeKind::Bool => UnionFindNode::new(UFTypeVar_::singleton(
                TypeCtor::Bool,
                UFType::Bool(provs_single),
            )),
            STypeKind::String => UnionFindNode::new(UFTypeVar_::singleton(
                TypeCtor::String,
                UFType::String(provs_single),
            )),
        }
    }

    fn add_constraint(&mut self, constraint: Constraint) {
        let mut add_hole_and_t = |hole: Rc<SType>, t: Rc<SType>| {
            let mut hole_node = self.retrieve_and_or_add_node(hole);
            let mut t_node = self.retrieve_and_or_add_node(t);
            hole_node.union_with(&mut t_node, UFTypeVar_::merge);
        };
        match (&constraint.expected.typekind, &constraint.actual.typekind) {
            (STypeKind::Unknown, _t) => {
                let hole = constraint.expected.clone();
                let t = constraint.actual.clone();
                add_hole_and_t(hole, t);
            }
            (_t, STypeKind::Unknown) => {
                let hole = constraint.actual.clone();
                let t = constraint.expected.clone();
                add_hole_and_t(hole, t);
            }
            _ => {}
        }
    }
}

fn fmt_type_suggestions(types: &Vec<&UFType>, f: &mut dyn Write) -> fmt::Result {
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

#[derive(Debug, Clone, PartialEq)]
pub struct UFTypeVar_ {
    types: BTreeMap<TypeCtor, UFType>,
}

impl UFTypeVar_ {
    fn empty() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    fn singleton(ctor: TypeCtor, t: UFType) -> Self {
        Self {
            types: {
                let mut s = BTreeMap::new();
                s.insert(ctor, t);
                s
            },
        }
    }

    // TODO: occurs check
    fn extend(&mut self, ctor: TypeCtor, mut t_other: UFType) {
        if let Some(mut t) = self.types.get_mut(&ctor) {
            match t_other {
                UFType::Unit(other_provs)
                | UFType::Int(other_provs)
                | UFType::Bool(other_provs)
                | UFType::String(other_provs) => {
                    t.provs_mut().extend(other_provs);
                }
                UFType::Function(other_provs, ref mut args_other, ref mut out_other) => {
                    match &mut t {
                        UFType::Function(t_provs, ref mut args, ref mut out) => {
                            if args.len() != args_other.len() {
                                panic!("should be same arity");
                            }
                            t_provs.extend(other_provs);
                            for i in 0..args.len() {
                                let (t_arg, other_arg) = (&mut args[i], &mut args_other[i]);
                                t_arg.union_with(other_arg, UFTypeVar_::merge);
                            }
                            out.union_with(out_other, UFTypeVar_::merge);
                        }
                        _ => panic!("ctor should be function"),
                    }
                }
                UFType::Tuple(other_provs, ref mut elements_other) => match &mut t {
                    UFType::Tuple(t_provs, ref mut elements) => {
                        if elements.len() != elements_other.len() {
                            panic!("should be same arity");
                        }
                        t_provs.extend(other_provs);
                        for i in 0..elements.len() {
                            let (t_arg, other_arg) = (&mut elements[i], &mut elements_other[i]);
                            t_arg.union_with(other_arg, UFTypeVar_::merge);
                        }
                    }
                    _ => panic!("ctor should be tuple"),
                },
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
pub fn result_of_constraint_solving(
    solution_map: SolutionMap,
    node_map: ast::NodeMap,
    source: &str,
) -> Result<(), String> {
    // TODO: you should assert that every node in the AST is in unsovled_type_suggestions_to_unknown_ty, solved or not!
    let mut type_conflicts = HashSet::new();
    for potential_types in solution_map.values() {
        // let type_suggestions = condense_candidates(potential_types);
        let type_suggestions = potential_types.clone_data().types;
        if type_suggestions.len() > 1 {
            type_conflicts.insert(type_suggestions);
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
            types_sorted.sort_by_key(|ty| match ty {
                UFType::Unit(provs)
                | UFType::Int(provs)
                | UFType::Bool(provs)
                | UFType::String(provs)
                | UFType::Function(provs, _, _)
                | UFType::Tuple(provs, _) => provs.len(),
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
                UFType::Unit(_) => err_string.push_str("Sources of void:\n"),
                UFType::Int(_) => err_string.push_str("Sources of int:\n"),
                UFType::Bool(_) => err_string.push_str("Sources of bool:\n"),
                UFType::String(_) => err_string.push_str("Sources of string:\n"),
                UFType::Function(_, args, _) => err_string.push_str(&format!(
                    "Sources of function with {} arguments:\n",
                    args.len()
                )),
                UFType::Tuple(_, elems) => err_string.push_str(&format!(
                    "Sources of tuple with {} elements:\n",
                    elems.len()
                )),
            };
            let provs = ty.provs();
            let mut provs_vec = provs.iter().collect::<Vec<_>>();
            provs_vec.sort_by_key(|prov| match prov {
                Prov::Builtin(_) => 0,
                Prov::Node(id) => node_map.get(id).unwrap().span().lo,
                Prov::FuncArg(_, _) => 2,
                Prov::FuncOut(_) => 2,
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
                    Box::new(Prov::Builtin("print: string -> void".to_string())),
                    0,
                ))],
                SType::make_unit(Prov::FuncArg(
                    Box::new(Prov::Builtin("print: string -> void".to_string())),
                    1,
                )),
            ),
            prov: Prov::Builtin("print: string -> void".to_string()),
        }),
    );
    ctx.borrow_mut().extend(
        &String::from("string_of_int"),
        Rc::new(SType {
            typekind: STypeKind::Arrow(
                vec![SType::make_int(Prov::FuncArg(
                    Box::new(Prov::Builtin("string_of_int: int -> string".to_string())),
                    0,
                ))],
                SType::make_string(Prov::FuncArg(
                    Box::new(Prov::Builtin("string_of_int: int -> string".to_string())),
                    1,
                )),
            ),
            prov: Prov::Builtin("string_of_int: int -> string".to_string()),
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
    solution_map: &mut SolutionMap,
) {
    let node_ty = SType::from_node(expr.clone());
    match mode {
        Mode::Syn => (),
        Mode::Ana { expected } => solution_map.add_constraint(Constraint {
            expected,
            actual: node_ty.clone(),
        }),
    };
    match &*expr.exprkind {
        ExprKind::Unit => {
            solution_map.add_constraint(Constraint {
                expected: node_ty,
                actual: SType::make_unit(Prov::Node(expr.id)),
            });
        }
        ExprKind::Int(_) => {
            solution_map.add_constraint(Constraint {
                expected: node_ty,
                actual: SType::make_int(Prov::Node(expr.id)),
            });
        }
        ExprKind::Bool(_) => {
            solution_map.add_constraint(Constraint {
                expected: node_ty,
                actual: SType::make_bool(Prov::Node(expr.id)),
            });
        }
        ExprKind::Str(_) => {
            solution_map.add_constraint(Constraint {
                expected: node_ty,
                actual: SType::make_string(Prov::Node(expr.id)),
            });
        }
        ExprKind::Var(id) => {
            let lookup = ctx.borrow_mut().lookup(id);
            if let Some(typ) = lookup {
                solution_map.add_constraint(Constraint {
                    expected: typ,
                    actual: node_ty,
                })
            }
        }
        ExprKind::BinOp(left, op, right) => {
            let (ty_left, ty_right, ty_out) = types_of_binop(op, expr.id);
            solution_map.add_constraint(Constraint {
                expected: ty_out,
                actual: node_ty,
            });
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
        ExprKind::Block(statements, opt_terminal_expr) => {
            let mut new_ctx = TyCtx::new(Some(ctx));
            for statement in statements {
                let updated = generate_constraints_stmt(
                    new_ctx.clone(),
                    Mode::Syn,
                    statement.clone(),
                    solution_map,
                );
                if let Some(ctx) = updated {
                    new_ctx = ctx
                }
            }
            if let Some(terminal_expr) = &opt_terminal_expr {
                generate_constraints_expr(
                    new_ctx,
                    Mode::Ana { expected: node_ty },
                    terminal_expr.clone(),
                    solution_map,
                )
            } else {
                solution_map.add_constraint(Constraint {
                    expected: node_ty,
                    actual: SType::make_unit(Prov::Node(expr.id)),
                })
            }
        }
        ExprKind::If(cond, expr1, expr2) => {
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana {
                    expected: SType::make_bool(Prov::Node(cond.id)),
                },
                cond.clone(),
                solution_map,
            );
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
        ExprKind::Func(args, out_annot, body) => {
            // arguments
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
                            solution_map,
                        )
                    } else {
                        generate_constraints_pat(
                            new_ctx.clone(),
                            Mode::Syn,
                            arg.clone(),
                            solution_map,
                        )
                    }
                    .unwrap_or(new_ctx.clone());
                    ty_pat
                })
                .collect();

            // body
            let ty_body = SType::make_unknown(Prov::FuncOut(Box::new(Prov::Node(expr.id))));
            generate_constraints_expr(
                new_ctx.clone(),
                Mode::Ana {
                    expected: ty_body.clone(),
                },
                body.clone(),
                solution_map,
            );
            if let Some(out_annot) = out_annot {
                generate_constraints_expr(
                    new_ctx,
                    Mode::Ana {
                        expected: ast_type_to_statics_type(out_annot.clone()),
                    },
                    body.clone(),
                    solution_map,
                );
            }

            // function type
            let ty_func = SType::make_arrow(ty_args, ty_body, expr.id);
            solution_map.add_constraint(Constraint {
                expected: ty_func,
                actual: node_ty,
            });
        }
        ExprKind::FuncAp(func, args) => {
            // arguments
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
                        solution_map,
                    );
                    unknown
                })
                .collect();

            // body
            let ty_body = SType::make_unknown(Prov::FuncOut(Box::new(Prov::Node(func.id))));
            solution_map.add_constraint(Constraint {
                expected: ty_body.clone(),
                actual: node_ty,
            });

            // function type
            let ty_func = SType::make_arrow(tys_args, ty_body, expr.id);
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
                .map(|expr| SType::make_unknown(Prov::Node(expr.id)))
                .collect();
            solution_map.add_constraint(Constraint {
                expected: SType::make_tuple(tys, expr.id),
                actual: node_ty,
            });
            for expr in exprs {
                generate_constraints_expr(ctx.clone(), Mode::Syn, expr.clone(), solution_map);
            }
        }
    }
}

pub fn generate_constraints_stmt(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    stmt: Rc<Stmt>,
    solution_map: &mut SolutionMap,
) -> Option<Rc<RefCell<TyCtx>>> {
    match &*stmt.stmtkind {
        StmtKind::Expr(expr) => {
            generate_constraints_expr(ctx, mode, expr.clone(), solution_map);
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
                    solution_map,
                )
            } else {
                generate_constraints_pat(ctx.clone(), Mode::Syn, pat.clone(), solution_map)
            };

            let ctx = new_ctx.unwrap_or(ctx);
            generate_constraints_expr(
                ctx.clone(),
                Mode::Ana { expected: ty_pat },
                expr.clone(),
                solution_map,
            );
            Some(ctx)
        }
    }
}

pub fn generate_constraints_pat(
    ctx: Rc<RefCell<TyCtx>>,
    mode: Mode,
    pat: Rc<Pat>,
    solution_map: &mut SolutionMap,
) -> Option<Rc<RefCell<TyCtx>>> {
    let mut new_ctx = TyCtx::new(Some(ctx));
    match &*pat.patkind {
        PatKind::Var(identifier) => {
            // letrec?: extend context with id and type before analyzing against said type
            let ty_pat = SType::from_node(pat.clone());
            new_ctx.borrow_mut().extend(identifier, ty_pat.clone());
            match mode {
                Mode::Syn => (),
                Mode::Ana { expected } => solution_map.add_constraint(Constraint {
                    expected,
                    actual: ty_pat,
                }),
            };
            Some(new_ctx)
        }
        PatKind::Tuple(pats) => {
            let tys = pats
                .iter()
                .map(|pat| SType::make_unknown(Prov::Node(pat.id)))
                .collect();
            solution_map.add_constraint(Constraint {
                expected: SType::make_tuple(tys, pat.id),
                actual: SType::from_node(pat.clone()),
            });
            for pat in pats {
                new_ctx =
                    generate_constraints_pat(new_ctx.clone(), Mode::Syn, pat.clone(), solution_map)
                        .unwrap_or(new_ctx);
            }
            Some(new_ctx)
        }
    }
}
