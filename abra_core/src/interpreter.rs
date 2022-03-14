use environment::Environment;
use operators::BinOpcode::*;
use operators::*;
use side_effects::Output::*;
use side_effects::*;
use std::cell::RefCell;
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

fn perform_op(val1: Rc<Expr>, op: BinOpcode, val2: Rc<Expr>) -> Rc<Expr> {
    match op {
        Add => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 + i2)),
            _ => panic!("one or more operands of Add are not Ints"),
        },
        Subtract => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 - i2)),
            _ => panic!("one or more operands of Subtract are not Ints"),
        },
        Multiply => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 * i2)),
            _ => panic!("one or more operands of Multiply are not Ints"),
        },
        Equals => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 == i2)),
            (Bool(b1), Bool(b2)) => Rc::new(Bool(b1 == b2)),
            _ => panic!("can only compare values which are both Ints or both Bools"),
        },
        GreaterThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 > i2)),
            _ => panic!("one or more operands of GreaterThan are not Ints"),
        },
        GreaterThanOrEquals => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 >= i2)),
            _ => panic!("one or more operands of GreaterThanOrEquals are not Ints"),
        },
        LessThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 < i2)),
            _ => panic!("one or more operands of LessThan are not Ints"),
        },
        LessThanOrEquals => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 <= i2)),
            _ => panic!("one or more operands of LessThanOrEquals are not Ints"),
        },
        _ => panic!("todo"),
    }
}

pub fn eval(expr: Rc<Expr>, env: Rc<RefCell<Environment>>, effects: &Effects) -> Rc<Expr> {
    match &*expr {
        Var(id) => {
            let result = env.borrow_mut().lookup(id);
            match result {
                None => panic!("No value for variable with id: {}", id),
                Some(val) => val,
            }
        }
        Unit | Int(_) | Bool(_) => expr.clone(),
        Func(id, ty1, ty2, body, _) => {
            let closure = Rc::new(RefCell::new(Environment::new(Some(env))));
            Rc::new(Func(
                id.clone(),
                ty1.clone(),
                ty2.clone(),
                body.clone(),
                closure,
            ))
        }
        BinOp(expr1, op, expr2) => {
            let val1 = eval(expr1.clone(), env.clone(), effects);
            let val2 = eval(expr2.clone(), env.clone(), effects);
            perform_op(val1, *op, val2)
        }
        Let(pat, _, expr1, expr2) => match &*pat.clone() {
            Pat::Var(id) => {
                let val = eval(expr1.clone(), env.clone(), effects);
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
                let val = match &*val {
                    // TODO: need to use weak reference?
                    //      may be a memory leak because closure has ref to new_env, but new_env contains ref to the val/Func()
                    //      which reference needs to be weak?
                    Func(id, ty1, ty2, body, _) => {
                        let closure =
                            Rc::new(RefCell::new(Environment::new(Some(new_env.clone()))));
                        Rc::new(Func(
                            id.clone(),
                            ty1.clone(),
                            ty2.clone(),
                            body.clone(),
                            closure,
                        ))
                    }
                    _ => val,
                };
                new_env.borrow_mut().extend(&id, val.clone());
                eval(expr2.clone(), new_env, effects)
            }
        },
        FuncAp(expr1, expr2) => {
            let val1 = eval(expr1.clone(), env.clone(), effects);
            let val2 = eval(expr2.clone(), env.clone(), effects);
            let (id, body, closure) = match &*val1.clone() {
                Func(id, _, _, body, closure) => (id.clone(), body.clone(), closure.clone()),
                _ => panic!("Left expression of FuncAp is not a function"),
            };
            let new_env = Rc::new(RefCell::new(Environment::new(Some(closure))));
            new_env.borrow_mut().extend(&id, val2.clone());
            // println!(
            //     "before eval, val2 is {:#?} and id is {} and body is {:#?} and env is {:#?}",
            //     val2, id, body, new_env
            // );
            eval(body, new_env, effects)
        }
        If(expr1, expr2, expr3) => {
            let val1 = eval(expr1.clone(), env.clone(), effects);
            match &*val1 {
                Bool(true) => eval(expr2.clone(), env.clone(), effects),
                Bool(false) => eval(expr3.clone(), env.clone(), effects),
                _ => panic!("If expression clause did not evaluate to a bool"),
            }
        }
    }
}
