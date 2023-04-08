use crate::ast::{
    self, ast_type_to_statics_type, Expr, ExprKind, Identifier, Pat, PatKind, Stmt, StmtKind,
};
use crate::operators::BinOpcode;
use disjoint_sets::UnionFindNode;
use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::fmt::{self, Write};
use std::rc::Rc;

type TypeVar = UnionFindNode<UFTypeVar_>;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Copy)]
pub enum TypeCtor {
    Unit,
    Int,
    Bool,
    String,
    Arrow(u8),
    Tuple(u8),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub enum Type {
    Var(TypeVar),
    Unit(Provs),
    Int(Provs),
    Bool(Provs),
    String(Provs),
    Function(Provs, Vec<Type>, Box<Type>), // TODO; just use Vec<Type> and Type for children
    Tuple(Provs, Vec<Type>),               // TODO remove this ctor if you can
}

impl Type {
    pub fn ctor(&self) -> TypeCtor {
        match self {
            Type::Var(_) => panic!("Type::ctor called on Type::Var"),
            Type::Unit(_) => TypeCtor::Unit,
            Type::Int(_) => TypeCtor::Int,
            Type::Bool(_) => TypeCtor::Bool,
            Type::String(_) => TypeCtor::String,
            Type::Function(_, args, _) => TypeCtor::Arrow(args.len() as u8),
            Type::Tuple(_, elems) => TypeCtor::Tuple(elems.len() as u8),
        }
    }

    pub fn from_node(solution_map: &mut SolutionMap, id: ast::Id) -> Type {
        let prov = Prov::Node(id);
        Type::make_var(solution_map, prov)
    }

    pub fn make_var(solution_map: &mut SolutionMap, prov: Prov) -> Type {
        match solution_map.get(&prov) {
            Some(ty) => Type::Var(ty.clone()),
            None => {
                let ty_var = TypeVar::new(UFTypeVar_::empty());
                let ty = Type::Var(ty_var.clone());
                solution_map.insert(prov, ty_var);
                ty
            }
        }
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Prov {
    Node(ast::Id),
    Builtin(String), // a builtin function or constant, which doesn't exist in the AST

    // INVARIANT: the provenances in FuncArg and FuncOut are either Node or Builtin.
    FuncArg(Box<Prov>, u8), // u8 represents the index of the argument
    FuncOut(Box<Prov>),     // u8 represents how many arguments before this output
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

impl fmt::Display for Type {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Type::Var(_) => write!(f, "?"),
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
                    write!(f, "{:#?}", elem)?;
                }
                write!(f, ")")
            }
        }
    }
}

impl Type {
    pub fn provs(&self) -> &Provs {
        match self {
            Self::Var(_) => panic!("Type::provs called on Type::Var"),
            Self::Unit(provs)
            | Self::Int(provs)
            | Self::Bool(provs)
            | Self::String(provs)
            | Self::Function(provs, _, _)
            | Self::Tuple(provs, _) => provs,
        }
    }
}

pub type Provs = RefCell<BTreeSet<Prov>>;

pub fn provs_singleton(prov: Prov) -> Provs {
    let mut set = BTreeSet::new();
    set.insert(prov);
    RefCell::new(set)
}

pub type SolutionMap = HashMap<Prov, TypeVar>;
trait SolutionMapTrait {}

fn fmt_type_suggestions(types: &Vec<&Type>, f: &mut dyn Write) -> fmt::Result {
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
    types: BTreeMap<TypeCtor, Type>,
}

impl UFTypeVar_ {
    fn empty() -> Self {
        Self {
            types: BTreeMap::new(),
        }
    }

    fn singleton(ctor: TypeCtor, t: Type) -> Self {
        Self {
            types: {
                let mut s = BTreeMap::new();
                s.insert(ctor, t);
                s
            },
        }
    }

    // TODO: occurs check
    fn extend(&mut self, t_other: Type) {
        let ctor = t_other.ctor();
        if let Some(t) = self.types.get_mut(&ctor) {
            match &t_other {
                Type::Var(_) => panic!("should not be Type::Var"),
                Type::Unit(other_provs)
                | Type::Int(other_provs)
                | Type::Bool(other_provs)
                | Type::String(other_provs) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone())
                }
                Type::Function(other_provs, args1, out1) => {
                    t.provs().borrow_mut().extend(other_provs.borrow().clone());
                    if let Type::Function(_, args2, out2) = t {
                        if args1.len() == args2.len() {
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
                            for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                                constrain(elem.clone(), elem2.clone());
                            }
                        }
                    }
                }
            }
        } else {
            self.types.insert(ctor, t_other);
        }
    }

    // TODO: occurs check
    fn merge(first: Self, second: Self) -> Self {
        let mut merged_types = Self { types: first.types };
        for (_ctor, t) in second.types {
            merged_types.extend(t);
        }
        merged_types
    }
}

fn constrain(expected: Type, actual: Type) {
    match (expected, actual) {
        (Type::Var(ref mut tvar), Type::Var(ref mut tvar2)) => {
            tvar.union_with(tvar2, UFTypeVar_::merge);
        }
        (t, Type::Var(tvar)) | (Type::Var(tvar), t) => {
            let mut data = tvar.clone_data();
            data.extend(t);
            tvar.replace_data(data);
        }
        (Type::Function(_, args1, out1), Type::Function(_, args2, out2)) => {
            if args1.len() == args2.len() {
                for (arg, arg2) in args1.iter().zip(args2.iter()) {
                    constrain(arg.clone(), arg2.clone());
                }
                constrain(*out1, *out2);
            }
        }
        (Type::Tuple(_, elems1), Type::Tuple(_, elems2)) => {
            if elems1.len() == elems2.len() {
                for (elem, elem2) in elems1.iter().zip(elems2.iter()) {
                    constrain(elem.clone(), elem2.clone());
                }
            }
        }
        _ => {}
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
    let mut type_conflicts = Vec::new();
    for potential_types in solution_map.values() {
        // let type_suggestions = condense_candidates(potential_types);
        let type_suggestions = potential_types.clone_data().types;
        if type_suggestions.len() > 1 && (!type_conflicts.contains(&type_suggestions)) {
            type_conflicts.push(type_suggestions);
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
        fmt_type_suggestions(&type_conflict, &mut err_string).unwrap();
        writeln!(err_string).unwrap();
        for ty in type_conflict {
            err_string.push('\n');
            match &ty {
                Type::Var(_) => err_string.push_str("Sources of var:\n"), // idk about this
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
    vars: HashMap<Identifier, Type>,
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
            Type::make_unit(Prov::FuncArg(
                Box::new(Prov::Builtin("print: string -> void".to_string())),
                1,
            ))
            .into(),
        ),
    );
    ctx.borrow_mut().extend(
        &String::from("string_of_int"),
        Type::Function(
            RefCell::new(BTreeSet::new()),
            vec![Type::make_int(Prov::FuncArg(
                Box::new(Prov::Builtin("string_of_int: int -> string".to_string())),
                0,
            ))],
            Type::make_string(Prov::FuncArg(
                Box::new(Prov::Builtin("string_of_int: int -> string".to_string())),
                1,
            ))
            .into(),
        ),
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
                constrain(typ, node_ty)
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
                    let ty_pat = Type::from_node(solution_map, arg.id);
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
            let ty_body =
                Type::make_var(solution_map, Prov::FuncOut(Box::new(Prov::Node(expr.id))));
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
            let ty_func = Type::make_arrow(ty_args, ty_body, expr.id);
            constrain(ty_func, node_ty);
        }
        ExprKind::FuncAp(func, args) => {
            // arguments
            let tys_args: Vec<Type> = args
                .iter()
                .enumerate()
                .map(|(n, arg)| {
                    let unknown = Type::make_var(
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
                Type::make_var(solution_map, Prov::FuncOut(Box::new(Prov::Node(func.id))));
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
                .map(|expr| Type::make_var(solution_map, Prov::Node(expr.id)))
                .collect();
            constrain(Type::make_tuple(tys, expr.id), node_ty);
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
            let ty_pat = Type::from_node(solution_map, pat.id);
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
            let ty_pat = Type::from_node(solution_map, pat.id);
            new_ctx.borrow_mut().extend(identifier, ty_pat.clone());
            match mode {
                Mode::Syn => (),
                Mode::Ana { expected } => constrain(expected, ty_pat),
            };
            Some(new_ctx)
        }
        PatKind::Tuple(pats) => {
            let tys = pats
                .iter()
                .map(|pat| Type::make_var(solution_map, Prov::Node(pat.id)))
                .collect();
            let actual = Type::from_node(solution_map, pat.id);
            constrain(Type::make_tuple(tys, pat.id), actual);
            for pat in pats {
                new_ctx =
                    generate_constraints_pat(new_ctx.clone(), Mode::Syn, pat.clone(), solution_map)
                        .unwrap_or(new_ctx);
            }
            Some(new_ctx)
        }
    }
}
