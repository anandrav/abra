use operators::BinOpcode::*;
use operators::*;
use side_effects::Output::*;
use side_effects::*;
use std::rc::Rc;
use typed_tree::Expr::*;
use typed_tree::*;

pub struct Effects {
    outputs: Vec<Output>,
}

impl Effects {
    pub fn empty() -> Effects {
        Effects {
            outputs: Vec::new(),
        }
    }
}

fn subst(expr1: Rc<Expr>, id: &Identifier, expr2: Rc<Expr>) -> Rc<Expr> {
    match &*expr2 {
        Var(sub_id) => {
            if sub_id == id {
                expr1
            } else {
                expr2
            }
        }
        Unit | Int(_) | Bool(_) => expr2,
        BinOp(sub_expr1, op, sub_expr2) => Rc::new(BinOp(
            subst(expr1.clone(), id, sub_expr1.clone()),
            *op,
            subst(expr1, id, sub_expr2.clone()),
        )),
        Let(pat, typ, sub_expr1, sub_expr2) => {
            let sub_expr1 = subst(expr1.clone(), id, sub_expr1.clone());
            match &*pat.clone() {
                Pat::Var(sub_id) => {
                    if sub_id == id {
                        expr2
                    } else {
                        Rc::new(Let(
                            pat.clone(),
                            *typ,
                            sub_expr1,
                            subst(expr1, id, sub_expr2.clone()),
                        ))
                    }
                }
            }
        }
        Func(sub_id, typ1, typ2, body) => {
            if sub_id == id {
                expr2
            } else {
                Rc::new(Func(
                    sub_id.clone(),
                    *typ1,
                    *typ2,
                    subst(expr1, id, body.clone()),
                ))
            }
        }
        FuncAp(sub_expr1, sub_expr2) => Rc::new(FuncAp(
            subst(expr1.clone(), id, sub_expr1.clone()),
            subst(expr1, id, sub_expr2.clone()),
        )),
        If(sub_expr1, sub_expr2, sub_expr3) => Rc::new(If(
            subst(expr1.clone(), id, sub_expr1.clone()),
            subst(expr1.clone(), id, sub_expr2.clone()),
            subst(expr1, id, sub_expr3.clone()),
        )),
        _ => panic!("todo"),
    }
}

fn perform_op(expr1: Rc<Expr>, op: BinOpcode, expr2: Rc<Expr>) -> Rc<Expr> {
    match op {
        Add => match (&*expr1, &*expr2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 + i2)),
            _ => panic!("one or more operands of Add are not Ints"),
        },
        Subtract => match (&*expr1, &*expr2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 - i2)),
            _ => panic!("one or more operands of Subtract are not Ints"),
        },
        Multiply => match (&*expr1, &*expr2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 * i2)),
            _ => panic!("one or more operands of Multiply are not Ints"),
        },
        _ => panic!("todo"),
    }
}

pub fn eval(expr: Rc<Expr>, effects: &Effects) -> Rc<Expr> {
    match &*expr {
        Var(id) => {
            panic!("Var should have been substituted before runtime");
        }
        Unit | Int(_) | Bool(_) | Func(_, _, _, _) => expr.clone(),
        BinOp(expr1, op, expr2) => {
            let val1 = eval(expr1.clone(), effects);
            let val2 = eval(expr2.clone(), effects);
            perform_op(val1, *op, val2)
        }
        Let(pat, _, expr1, expr2) => match &*pat.clone() {
            Pat::Var(id) => {
                let val = eval(expr1.clone(), effects);
                let expr2 = subst(val, &id, expr2.clone());
                eval(expr2, effects)
            }
        },
        FuncAp(expr1, expr2) => {
            let val1 = eval(expr1.clone(), effects);
            let val2 = eval(expr2.clone(), effects);
            let (id, body) = match &*val1.clone() {
                Func(id, _, _, body) => (id.clone(), body.clone()),
                _ => panic!("Left expression of FuncAp is not a function"),
            };
            println!(
                "before substitution, val2 is {:#?} and id is {} and body is {:#?}",
                val2, id, body
            );
            let val = subst(val2, &id, body.clone());
            println!("after substitution, bodyval is {:#?}", val);
            eval(val, effects)
        }
        If(expr1, expr2, expr3) => {
            let val1 = eval(expr1.clone(), effects);
            match &*val1 {
                Bool(true) => eval(expr2.clone(), effects),
                Bool(false) => eval(expr3.clone(), effects),
                _ => panic!("If expression clause did not evaluate to a bool"),
            }
        }
        _ => panic!("todo"),
    }
}
