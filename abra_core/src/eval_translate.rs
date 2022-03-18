use environment::Environment;
use eval_tree;
use parse_tree;
use std::cell::RefCell;
use std::rc::Rc;
use typed_tree;
use types::Type;

type Tte = typed_tree::Expr;
type Ete = eval_tree::Expr;

type Ttp = typed_tree::Pat;
type Etp = eval_tree::Pat;

pub fn translate_pat(parse_tree: Rc<Ttp>) -> Rc<Etp> {
    match &*parse_tree {
        Ttp::Var(id) => Rc::new(Etp::Var(id.clone())),
    }
}

pub fn translate_expr_func(
    (id, t_in): typed_tree::FuncArg,
    func_args: Vec<typed_tree::FuncArg>,
    t_out: Rc<Type>,
    body: Rc<Tte>,
) -> Rc<Ete> {
    if func_args.is_empty() {
        Rc::new(Ete::Func(
            id.clone(),
            t_in.clone(),
            t_out.clone(),
            translate_expr(body.clone()),
            Rc::new(RefCell::new(Environment::new(None))),
        ))
    } else {
        let rest_of_function = translate_expr_func(
            func_args[0].clone(),
            func_args[1..].to_vec(),
            t_out.clone(), // todo this definitely is wrong
            body.clone(),
        );
        Rc::new(Ete::Func(
            id.clone(),
            t_in.clone(),
            t_out.clone(),
            rest_of_function,
            Rc::new(RefCell::new(Environment::new(None))),
        ))
    }
}

pub fn translate_expr_ap(expr1: Rc<Tte>, expr2: Rc<Tte>, exprs: Vec<Rc<Tte>>) -> Rc<Ete> {
    if exprs.is_empty() {
        Rc::new(Ete::FuncAp(translate_expr(expr1), translate_expr(expr2)))
    } else {
        let rest_of_arguments_applied =
            translate_expr_ap(expr1.clone(), expr2, exprs[..exprs.len() - 1].to_vec());
        Rc::new(Ete::FuncAp(
            rest_of_arguments_applied,
            translate_expr(exprs.last().unwrap().clone()),
        ))
    }
}

pub fn translate_expr(parse_tree: Rc<Tte>) -> Rc<Ete> {
    match &*parse_tree {
        Tte::Var(id) => Rc::new(Ete::Var(id.clone())),
        Tte::Unit => Rc::new(Ete::Unit),
        Tte::Int(i) => Rc::new(Ete::Int(*i)),
        Tte::Bool(b) => Rc::new(Ete::Bool(*b)),
        Tte::Str(s) => Rc::new(Ete::Str(s.clone())),
        Tte::BinOp(expr1, op, expr2) => Rc::new(Ete::BinOp(
            translate_expr(expr1.clone()),
            *op,
            translate_expr(expr2.clone()),
        )),
        Tte::Let(pat, t, expr1, expr2) => Rc::new(Ete::Let(
            translate_pat(pat.clone()),
            t.clone(),
            translate_expr(expr1.clone()),
            translate_expr(expr2.clone()),
        )),
        Tte::Func(func_arg, func_args, t_out, body) => translate_expr_func(
            func_arg.clone(),
            func_args.clone(),
            t_out.clone(),
            body.clone(),
        ),
        Tte::FuncAp(expr1, expr2, exprs) => {
            translate_expr_ap(expr1.clone(), expr2.clone(), exprs.clone())
        }
        Tte::If(expr1, expr2, expr3) => Rc::new(Ete::If(
            translate_expr(expr1.clone()),
            translate_expr(expr2.clone()),
            translate_expr(expr3.clone()),
        )),
    }
}
