use parse_tree;
use std::rc::Rc;
use typed_tree;
use types::Type;

type pte = parse_tree::Expr;
type tte = typed_tree::Expr;

type ptp = parse_tree::Pat;
type ttp = typed_tree::Pat;

type Constraint = (Type, Type);

type Identifier = String;
struct Assumption {
    id: Identifier,
    typ: Type,
}
struct Context {
    assumptions: Vec<Assumption>,
}

impl Context {
    fn lookup(&self, id: &Identifier) -> Option<Type> {
        for a in &self.assumptions {
            if a.id == *id {
                return Some(a.typ);
            }
        }
        return None;
    }

    fn extend(&self, a: Assumption) {}
}

pub fn strip_options_pat(parse_tree: Rc<ptp>) -> Rc<ttp> {
    match &*parse_tree {
        ptp::Var(id) => Rc::new(ttp::Var(id.clone())),
    }
}

pub fn strip_options_expr(parse_tree: Rc<pte>) -> Rc<tte> {
    match &*parse_tree {
        pte::Var(id) => Rc::new(tte::Var(id.clone())),
        pte::Unit => Rc::new(tte::Unit),
        pte::Int(i) => Rc::new(tte::Int(*i)),
        pte::Bool(b) => Rc::new(tte::Bool(*b)),
        pte::BinOp(expr1, op, expr2) => Rc::new(tte::BinOp(
            strip_options_expr(expr1.clone()),
            *op,
            strip_options_expr(expr2.clone()),
        )),
        pte::Let(pat, t, expr1, expr2) => Rc::new(tte::Let(
            strip_options_pat(pat.clone()),
            t.unwrap(),
            strip_options_expr(expr1.clone()),
            strip_options_expr(expr2.clone()),
        )),
        pte::Func(id, t_in, t_out, expr) => Rc::new(tte::Func(
            id.clone(),
            t_in.unwrap(),
            t_out.unwrap(),
            strip_options_expr(expr.clone()),
        )),
        pte::FuncAp(expr1, expr2) => Rc::new(tte::FuncAp(
            strip_options_expr(expr1.clone()),
            strip_options_expr(expr2.clone()),
        )),
        pte::If(expr1, expr2, expr3) => Rc::new(tte::If(
            strip_options_expr(expr1.clone()),
            strip_options_expr(expr2.clone()),
            strip_options_expr(expr3.clone()),
        )),
        pte::Match(_, _) => {
            panic!("todo");
        }
    }
}

// pub fn syn(ctx: &Context, e: Box<parse_tree::Expr>) -> (Type, Vec<Constraint>) {
//     match e {
//         Var(s) ->
//     }
// }
