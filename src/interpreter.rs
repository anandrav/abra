use crate::environment::Environment;
use crate::eval_tree::Expr::*;
use crate::eval_tree::*;
use crate::operators::BinOpcode::*;
use crate::operators::*;
use crate::side_effects;
use crate::side_effects::*;
use std::cell::RefCell;
use std::rc::Rc;

pub fn make_new_environment() -> Rc<RefCell<Environment>> {
    let env = Rc::new(RefCell::new(Environment::new(None)));
    env.borrow_mut().extend(
        &String::from("print"),
        Rc::new(Expr::Func(
            String::from("str"),
            Rc::new(Expr::EffectAp(
                side_effects::Effect::Print,
                vec![Rc::new(Expr::Var(String::from("str")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("string_of_int"),
        Rc::new(Expr::Func(
            String::from("some_int"),
            Rc::new(Expr::EffectAp(
                side_effects::Effect::StringOfInt,
                vec![Rc::new(Expr::Var(String::from("some_int")))],
            )),
            None,
        )),
    );
    env
}

pub struct Interpreter {
    program_expr: Rc<Expr>,
    env: Rc<RefCell<Environment>>,
    next_input: Option<Input>,
}

impl Interpreter {
    pub fn new(program_expr: Rc<Expr>) -> Self {
        Interpreter {
            program_expr,
            env: make_new_environment(),
            next_input: None,
        }
    }

    pub fn is_finished(&self) -> bool {
        is_val(&self.program_expr)
    }

    pub fn get_val(&self) -> Option<Rc<Expr>> {
        if self.is_finished() {
            Some(self.program_expr.clone())
        } else {
            None
        }
    }

    pub fn run(
        &mut self,
        mut effect_handler: impl FnMut(Effect, Vec<Rc<Expr>>) -> Input,
        steps: i32,
    ) {
        let result = interpret(
            self.program_expr.clone(),
            self.env.clone(),
            steps,
            &self.next_input,
        );
        self.program_expr = result.expr;
        self.env = result.new_env;
        self.next_input = result
            .effect
            .map(|(effect, args)| effect_handler(effect, args))
    }
}

// todo anand: separate into two cases: Success and Failure... new_env should only be present for failure,
// steps should only be <= 0 and/or effect should be present for failure...
pub struct InterpretResult {
    pub expr: Rc<Expr>,
    pub steps: i32,
    pub effect: Option<(side_effects::Effect, Vec<Rc<Expr>>)>,
    pub new_env: Rc<RefCell<Environment>>,
}

fn interpret(
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
                    new_env: env,
                },
            }
        }
        Unit | Int(_) | Bool(_) | Str(_) | Func(_, _, Some(_)) => InterpretResult {
            expr: expr.clone(),
            steps,
            effect: None,
            new_env: env,
        },
        Func(id, body, None) => {
            // todo anand: closure is getting overwritten when another parital execution happens and it forgets about variiables...
            let closure = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
            InterpretResult {
                expr: Rc::new(Func(id.clone(), body.clone(), Some(closure))),
                steps,
                effect: None,
                new_env: env,
            }
        }
        BinOp(expr1, op, expr2) => {
            let InterpretResult {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(BinOp(expr1, *op, expr2.clone())),
                    steps,
                    effect,
                    new_env,
                };
            }
            let InterpretResult {
                expr: expr2,
                steps,
                effect,
                new_env,
            } = interpret(expr2.clone(), env.clone(), steps, input);
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(BinOp(expr1, *op, expr2)),
                    steps,
                    effect,
                    new_env,
                };
            }
            let val = perform_op(expr1, *op, expr2);
            let steps = steps - 1;
            InterpretResult {
                expr: val,
                steps,
                effect: None,
                new_env: env,
            }
        }
        Let(pat, expr1, expr2) => match &*pat.clone() {
            Pat::Var(id) => {
                let InterpretResult {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
                if effect.is_some() || steps <= 0 {
                    return InterpretResult {
                        expr: Rc::new(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    };
                }
                // todo anand: explain this with comment
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
                let expr1 = match &*expr1 {
                    // TODO: need to use weak reference?
                    //      may be a memory leak because closure has ref to new_env, but new_env contains ref to the val/Func()
                    //      ... which reference needs to be weak??
                    Func(id, body, _) => {
                        let closure =
                            Rc::new(RefCell::new(Environment::new(Some(new_env.clone()))));
                        Rc::new(Func(id.clone(), body.clone(), Some(closure)))
                    }
                    _ => expr1,
                };
                new_env.borrow_mut().extend(id, expr1);

                let InterpretResult {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(expr2.clone(), new_env, steps, input);
                if effect.is_some() || steps <= 0 {
                    return InterpretResult {
                        expr, // todo anand: I think this should just be "expr" here
                        steps,
                        effect,
                        new_env,
                    };
                }
                InterpretResult {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                }
            }
        },
        FuncAp(expr1, expr2, funcapp_env) => {
            let InterpretResult {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(FuncAp(expr1, expr2.clone(), funcapp_env.clone())),
                    steps,
                    effect,
                    new_env,
                };
            }
            let InterpretResult {
                expr: expr2,
                steps,
                effect,
                new_env,
            } = interpret(expr2.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(FuncAp(expr1, expr2, funcapp_env.clone())),
                    steps,
                    effect,
                    new_env,
                };
            }
            let (id, body, closure) = match &*expr1 {
                Func(id, body, closure) => match closure {
                    None => (
                        id,
                        body,
                        Rc::new(RefCell::new(Environment::new(Some(env.clone())))),
                    ),
                    Some(closure) => (id, body, closure.clone()),
                },
                _ => panic!("not a function"),
            };
            let funcapp_env = match funcapp_env {
                Some(funcapp_env) => funcapp_env.clone(),
                None => {
                    let funcapp_env =
                        Rc::new(RefCell::new(Environment::new(Some(closure.clone()))));
                    funcapp_env.borrow_mut().extend(id, expr2.clone());
                    funcapp_env
                }
            };

            // TODO consume a step if interpret result is success, but only after! that's hwne funcapp is done.
            // let result = interpret(body, funcapp_env, steps, input);
            // debug_println!("then env is {:#?}", result.new_env);
            // return InterpretResult {
            //     expr: Rc::new(FuncAp(expr1, result.expr)),
            //     steps: result.steps,
            //     effect: result.effect,
            //     new_env,
            // };

            let InterpretResult {
                expr: body,
                steps,
                effect,
                new_env: funcapp_env,
            } = interpret(body.clone(), funcapp_env, steps, input);
            // if didn't finish executing for the body of function application,
            // return a FuncApp for the expression field and set environment to new_env... So we can try again later.
            // Can't return funcapp_env for environment! Because it only contains the closure and the function's arguments!
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(FuncAp(
                        Rc::new(Func(id.clone(), body, Some(closure))),
                        expr2,
                        Some(funcapp_env),
                    )),
                    steps,
                    effect,
                    new_env,
                };
            }
            InterpretResult {
                expr: body,
                steps,
                effect,
                new_env: env, // return env to normal
            }
        }
        If(expr1, expr2, expr3) => {
            let InterpretResult {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(expr1.clone(), env.clone(), steps, &input.clone());
            if effect.is_some() || steps <= 0 {
                return InterpretResult {
                    expr: Rc::new(If(expr1, expr2.clone(), expr3.clone())),
                    steps,
                    effect,
                    new_env,
                };
            }
            match &*expr1 {
                Bool(true) => {
                    let InterpretResult {
                        expr: expr2,
                        steps,
                        effect,
                        new_env,
                    } = interpret(expr2.clone(), env.clone(), steps, input);
                    if effect.is_some() || steps <= 0 {
                        return InterpretResult {
                            expr: expr2,
                            steps,
                            effect,
                            new_env,
                        };
                    }
                    let steps = steps - 1;
                    InterpretResult {
                        expr: expr2,
                        steps,
                        effect,
                        new_env: env,
                    }
                }
                Bool(false) => {
                    let InterpretResult {
                        expr: expr3,
                        steps,
                        effect,
                        new_env,
                    } = interpret(expr3.clone(), env.clone(), steps, input);
                    if effect.is_some() || steps <= 0 {
                        return InterpretResult {
                            expr: expr3,
                            steps,
                            effect,
                            new_env,
                        };
                    }
                    let steps = steps - 1;
                    InterpretResult {
                        expr: expr3,
                        steps,
                        effect,
                        new_env: env,
                    }
                }
                _ => panic!(
                    "If expression clause did not evaluate to a bool: {:#?}",
                    expr1
                ),
            }
        }
        EffectAp(effect_enum, args) => {
            let mut args = args.to_vec();
            for i in 0..args.len() {
                let InterpretResult {
                    expr: arg,
                    steps,
                    effect,
                    new_env,
                } = interpret(args[i].clone(), env.clone(), steps, &input.clone());
                args[i] = arg;
                if effect.is_some() || steps <= 0 {
                    return InterpretResult {
                        expr: Rc::new(EffectAp(effect_enum.clone(), args.to_vec())),
                        steps,
                        effect,
                        new_env,
                    };
                }
            }
            let steps = steps - 1;
            InterpretResult {
                expr: Rc::new(ConsumedEffect),
                steps,
                effect: Some((effect_enum.clone(), args.to_vec())),
                new_env: env,
            }
        }
        ConsumedEffect => match input {
            None => panic!("no input to substitute for ConsumedEffect"),
            Some(input) => match input {
                Input::Unit => InterpretResult {
                    expr: Rc::new(Unit),
                    steps,
                    effect: None,
                    new_env: env,
                },
                Input::Cin(string) => InterpretResult {
                    expr: Rc::new(Str(string.to_string())),
                    steps,
                    effect: None,
                    new_env: env,
                },
            },
        },
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
        Divide => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Int(i1 / i2)),
            _ => panic!("one or more operands of Divide are not Ints"),
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
        // GreaterThanOrEquals => match (&*val1, &*val2) {
        //     (Int(i1), Int(i2)) => Rc::new(Bool(i1 >= i2)),
        //     _ => panic!("one or more operands of GreaterThanOrEquals are not Ints"),
        // },
        LessThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Rc::new(Bool(i1 < i2)),
            _ => panic!("one or more operands of LessThan are not Ints"),
        },
        // LessThanOrEquals => match (&*val1, &*val2) {
        //     (Int(i1), Int(i2)) => Rc::new(Bool(i1 <= i2)),
        //     _ => panic!("one or more operands of LessThanOrEquals are not Ints"),
        // },
        // _ => panic!("operation not supported"),
    }
}
