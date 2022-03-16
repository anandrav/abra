use environment::Environment;
use parse_tree;
use std::cell::RefCell;
use std::rc::Rc;
use typed_tree;
// use types::Type;

type Pte = parse_tree::Expr;
type Tte = typed_tree::Expr;

type Ptp = parse_tree::Pat;
type Ttp = typed_tree::Pat;

// type Constraint = (Type, Type);

// type Identifier = String;
// struct Assumption {
//     id: Identifier,
//     typ: Type,
// }
// struct Context {
//     assumptions: Vec<Assumption>,
// }

// impl Context {
//     fn lookup(&self, id: &Identifier) -> Option<Type> {
//         for a in &self.assumptions {
//             if a.id == *id {
//                 return Some(a.typ);
//             }
//         }
//         return None;
//     }

//     fn extend(&self, a: Assumption) {}
// }

pub fn strip_options_pat(parse_tree: Rc<Ptp>) -> Rc<Ttp> {
    match &*parse_tree {
        Ptp::Var(id) => Rc::new(Ttp::Var(id.clone())),
    }
}

pub fn strip_options_expr(parse_tree: Rc<Pte>) -> Rc<Tte> {
    match &*parse_tree {
        Pte::Var(id) => Rc::new(Tte::Var(id.clone())),
        Pte::Unit => Rc::new(Tte::Unit),
        Pte::Int(i) => Rc::new(Tte::Int(*i)),
        Pte::Bool(b) => Rc::new(Tte::Bool(*b)),
        Pte::Str(s) => Rc::new(Tte::Str(s.clone())),
        Pte::BinOp(expr1, op, expr2) => Rc::new(Tte::BinOp(
            strip_options_expr(expr1.clone()),
            *op,
            strip_options_expr(expr2.clone()),
        )),
        Pte::Let(pat, t, expr1, expr2) => Rc::new(Tte::Let(
            strip_options_pat(pat.clone()),
            t.as_ref().unwrap().clone(),
            strip_options_expr(expr1.clone()),
            strip_options_expr(expr2.clone()),
        )),
        Pte::Func(id, t_in, t_out, expr) => Rc::new(Tte::Func(
            id.clone(),
            t_in.as_ref().unwrap().clone(),
            t_out.as_ref().unwrap().clone(),
            strip_options_expr(expr.clone()),
            Rc::new(RefCell::new(Environment::new(None))),
        )),
        Pte::FuncAp(expr1, expr2) => Rc::new(Tte::FuncAp(
            strip_options_expr(expr1.clone()),
            strip_options_expr(expr2.clone()),
        )),
        Pte::If(expr1, expr2, expr3) => Rc::new(Tte::If(
            strip_options_expr(expr1.clone()),
            strip_options_expr(expr2.clone()),
            strip_options_expr(expr3.clone()),
        )),
        Pte::Match(_, _) => {
            panic!("todo");
        }
    }
}

// pub fn syn(ctx: &Context, e: Box<parse_tree::Expr>) -> (Type, Vec<Constraint>) {
//     match e {
//         Var(s) ->
//     }
// }
