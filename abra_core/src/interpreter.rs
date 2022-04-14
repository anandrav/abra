use environment::Environment;
use eval_tree::Expr::*;
use eval_tree::*;
use operators::BinOpcode::*;
use operators::*;
use side_effects;
use side_effects::*;
use std::cell::RefCell;
use std::rc::Rc;

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

pub fn eval(expr: Rc<Expr>, env: Rc<RefCell<Environment>>) -> Rc<Expr> {
    match &*expr {
        Var(id) => {
            let result = env.borrow_mut().lookup(id);
            match result {
                None => panic!("No value for variable with id: {}", id),
                Some(val) => val,
            }
        }
        Unit | Int(_) | Bool(_) | Str(_) => expr.clone(),
        Func(id, body, _) => {
            let closure = Rc::new(RefCell::new(Environment::new(Some(env))));
            Rc::new(Func(id.clone(), body.clone(), closure))
        }
        BinOp(expr1, op, expr2) => {
            let val1 = eval(expr1.clone(), env.clone());
            let val2 = eval(expr2.clone(), env.clone());
            perform_op(val1, *op, val2)
        }
        Let(pat, expr1, expr2) => match &*pat.clone() {
            Pat::Var(id) => {
                let val = eval(expr1.clone(), env.clone());
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
                let val = match &*val {
                    // TODO: need to use weak reference?
                    //      may be a memory leak because closure has ref to new_env, but new_env contains ref to the val/Func()
                    //      which reference needs to be weak?
                    Func(id, body, _) => {
                        let closure =
                            Rc::new(RefCell::new(Environment::new(Some(new_env.clone()))));
                        Rc::new(Func(id.clone(), body.clone(), closure))
                    }
                    _ => val,
                };
                new_env.borrow_mut().extend(&id, val.clone());
                eval(expr2.clone(), new_env)
            }
        },
        FuncAp(expr1, expr2) => {
            let val1 = eval(expr1.clone(), env.clone());
            let val2 = eval(expr2.clone(), env.clone());
            let (id, body, closure) = match &*val1.clone() {
                Func(id, body, closure) => (id.clone(), body.clone(), closure.clone()),
                _ => panic!("Left expression of FuncAp is not a function"),
            };
            let new_env = Rc::new(RefCell::new(Environment::new(Some(closure))));
            new_env.borrow_mut().extend(&id, val2.clone());
            // println!(
            //     "before eval, val2 is {:#?} and id is {} and body is {:#?} and env is {:#?}",
            //     val2, id, body, new_env
            // );
            eval(body, new_env)
        }
        If(expr1, expr2, expr3) => {
            let val1 = eval(expr1.clone(), env.clone());
            match &*val1 {
                Bool(true) => eval(expr2.clone(), env.clone()),
                Bool(false) => eval(expr3.clone(), env.clone()),
                _ => panic!("If expression clause did not evaluate to a bool"),
            }
        }
        Effect(_) => panic!("Effects are not handled!"),
    }
}

pub struct InterpretResult {
    pub expr: Rc<Expr>,
    pub steps: i32,
    pub effect: Option<side_effects::Effect>,
}

pub fn interpret(
    expr: Rc<Expr>,
    env: Rc<RefCell<Environment>>,
    steps: i32,
    input: &Option<Input>,
) -> InterpretResult {
    match &*expr {
        Var(id) => {
            let result = env.borrow_mut().lookup(id);
            match result {
                None => panic!("No value for variable with id: {}", id),
                Some(val) => InterpretResult {
                    expr: val,
                    steps,
                    effect: None,
                },
            }
        }
        Unit | Int(_) | Bool(_) | Str(_) => InterpretResult {
            expr: expr.clone(),
            steps,
            effect: None,
        },
        Func(id, body, _) => {
            let closure = Rc::new(RefCell::new(Environment::new(Some(env))));
            InterpretResult {
                expr: Rc::new(Func(id.clone(), body.clone(), closure)),
                steps,
                effect: None,
            }
        }
        BinOp(expr1, op, expr2) => {
            let InterpretResult {
                expr: expr1,
                steps,
                effect,
            } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(BinOp(expr1, *op, expr2.clone())),
                    steps,
                    effect,
                };
            }
            let InterpretResult {
                expr: expr2,
                steps,
                effect,
            } = interpret(expr2.clone(), env.clone(), steps, input);
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(BinOp(expr1, *op, expr2.clone())),
                    steps,
                    effect,
                };
            }
            let val = perform_op(expr1, *op, expr2);
            let steps = steps - 1;
            InterpretResult {
                expr: val,
                steps,
                effect: None,
            }
        }
        Let(pat, expr1, expr2) => match &*pat.clone() {
            Pat::Var(id) => {
                let InterpretResult {
                    expr: expr1,
                    steps,
                    effect,
                } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
                if effect.is_some() || steps <= 0 {
                    return InterpretResult {
                        expr: Rc::new(Let(pat.clone(), expr1.clone(), expr2.clone())),
                        steps,
                        effect,
                    };
                }
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
                let expr1 = match &*expr1 {
                    // TODO: need to use weak reference?
                    //      may be a memory leak because closure has ref to new_env, but new_env contains ref to the val/Func()
                    //      which reference needs to be weak?
                    Func(id, body, _) => {
                        let closure =
                            Rc::new(RefCell::new(Environment::new(Some(new_env.clone()))));
                        Rc::new(Func(id.clone(), body.clone(), closure))
                    }
                    _ => expr1,
                };
                new_env.borrow_mut().extend(&id, expr1.clone());
                interpret(expr2.clone(), new_env, steps, input)
            }
        },
        FuncAp(expr1, expr2) => {
            let InterpretResult {
                expr: expr1,
                steps,
                effect,
            } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(FuncAp(expr1, expr2.clone())),
                    steps,
                    effect,
                };
            }
            let InterpretResult {
                expr: expr2,
                steps,
                effect,
            } = interpret(expr2.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(FuncAp(expr1, expr2)),
                    steps,
                    effect,
                };
            }
            let (id, body, closure) = match &*expr1.clone() {
                Func(id, body, closure) => (id.clone(), body.clone(), closure.clone()),
                _ => panic!("Left expression of FuncAp is not a function"),
            };
            let new_env = Rc::new(RefCell::new(Environment::new(Some(closure))));
            new_env.borrow_mut().extend(&id, expr2.clone());
            // println!(
            //     "before eval, val2 is {:#?} and id is {} and body is {:#?} and env is {:#?}",
            //     val2, id, body, new_env
            // );
            let steps = steps - 1;
            interpret(body, new_env, steps, input)
        }
        If(expr1, expr2, expr3) => {
            let InterpretResult {
                expr: expr1,
                steps,
                effect,
            } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(If(expr1, expr2.clone(), expr3.clone())),
                    steps,
                    effect,
                };
            }
            match &*expr1 {
                Bool(true) => {
                    let InterpretResult {
                        expr: expr2,
                        steps,
                        effect,
                    } = interpret(expr2.clone(), env.clone(), steps, input);
                    if effect.is_some() || steps <= 0 {
                        return InterpretResult {
                            expr: Rc::new(If(expr1, expr2, expr3.clone())),
                            steps,
                            effect,
                        };
                    }
                    let steps = steps - 1;
                    return InterpretResult {
                        expr: expr2,
                        steps,
                        effect,
                    };
                }
                Bool(false) => {
                    let InterpretResult {
                        expr: expr3,
                        steps,
                        effect,
                    } = interpret(expr3.clone(), env.clone(), steps, input);
                    if effect.is_some() || steps <= 0 {
                        return InterpretResult {
                            expr: Rc::new(If(expr1, expr2.clone(), expr3)),
                            steps,
                            effect,
                        };
                    }
                    let steps = steps - 1;
                    return InterpretResult {
                        expr: expr3,
                        steps,
                        effect,
                    };
                }
                _ => panic!("If expression clause did not evaluate to a bool"),
            }
        }
        Effect(_) => panic!("Effects are not handled"),
    }
}
