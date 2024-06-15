use crate::environment::Environment;
use crate::eval_tree::Expr::*;
use crate::eval_tree::*;
use crate::operators::BinOpcode::*;
use crate::operators::*;
use crate::side_effects::*;
use crate::statics::InferenceContext;
use crate::statics::SolvedType;
use crate::statics::TypeMonomorphized;
use crate::util::{shared, Shared};
use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

// TODO why do we have to manually call this?
pub(crate) fn add_builtins_and_variants<Effects: EffectTrait>(
    env: Rc<RefCell<Environment>>,
    inf_ctx: &InferenceContext,
) -> Rc<RefCell<Environment>> {
    // builtins
    env.borrow_mut().extend(
        &String::from("newline"),
        shared(Expr::Str(String::from("\n"))),
    );
    for (idx, eff) in Effects::enumerate().iter().enumerate() {
        let (arg_types, _ret_type) = eff.type_signature();
        let mut args = vec![];
        for (i, _) in arg_types.iter().enumerate() {
            args.push(format!("arg{}", i));
        }
        let body = shared(Expr::EffectAp(
            idx.try_into().unwrap(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, _)| shared(Expr::Var(format!("arg{}", i))))
                .collect(),
        ));
        let expr = shared(Expr::Func(args, body, None));
        env.borrow_mut().extend(&eff.function_name(), expr);
    }
    env.borrow_mut().extend(
        &String::from("equals_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::EqualsInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("equals_string"),
        shared(Expr::Func(
            vec![String::from("s1"), String::from("s2")],
            shared(Expr::BuiltinAp(
                Builtin::EqualsString,
                vec![
                    shared(Expr::Var(String::from("s1"))),
                    shared(Expr::Var(String::from("s2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("int_to_string"),
        shared(Expr::Func(
            vec![String::from("some_int")],
            shared(Expr::BuiltinAp(
                Builtin::IntToString,
                vec![shared(Expr::Var(String::from("some_int")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("float_to_string"),
        shared(Expr::Func(
            vec![String::from("some_float")],
            shared(Expr::BuiltinAp(
                Builtin::FloatToString,
                vec![shared(Expr::Var(String::from("some_float")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("to_float"),
        shared(Expr::Func(
            vec![String::from("some_int")],
            shared(Expr::BuiltinAp(
                Builtin::IntToFloat,
                vec![shared(Expr::Var(String::from("some_int")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("round"),
        shared(Expr::Func(
            vec![String::from("some_float")],
            shared(Expr::BuiltinAp(
                Builtin::RoundFloatToInt,
                vec![shared(Expr::Var(String::from("some_float")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("append_strings"),
        shared(Expr::Func(
            vec![String::from("s1"), String::from("s2")],
            shared(Expr::BuiltinAp(
                Builtin::AppendStrings,
                vec![
                    shared(Expr::Var(String::from("s1"))),
                    shared(Expr::Var(String::from("s2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("add_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::AddInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("minus_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::MinusInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("multiply_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::MultiplyInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("divide_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::DivideInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("pow_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::PowInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("less_than_int"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::LessThanInt,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("add_float"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::AddFloat,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("minus_float"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::MinusFloat,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("multiply_float"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::MultiplyFloat,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("divide_float"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::DivideFloat,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("pow_float"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::PowFloat,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("sqrt_float"),
        shared(Expr::Func(
            vec![String::from("f")],
            shared(Expr::BuiltinAp(
                Builtin::SqrtFloat,
                vec![shared(Expr::Var(String::from("f")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("less_than_float"),
        shared(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            shared(Expr::BuiltinAp(
                Builtin::LessThanFloat,
                vec![
                    shared(Expr::Var(String::from("i1"))),
                    shared(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    for (_name, adt_def) in inf_ctx.adt_defs.iter() {
        for variant in adt_def.variants.iter() {
            let ctor = &variant.ctor;
            if let SolvedType::Unit = variant.data.solution().unwrap() {
                env.borrow_mut().extend(
                    ctor,
                    shared(Expr::TaggedVariant(ctor.clone(), shared(Expr::Unit))),
                );
            } else {
                match &variant.data.solution().unwrap() {
                    SolvedType::Tuple(elems) => {
                        let mut args = vec![];
                        for (i, _) in elems.iter().enumerate() {
                            args.push(shared(Expr::Var(format!("arg{}", i))));
                        }
                        let body =
                            shared(Expr::TaggedVariant(ctor.clone(), shared(Expr::Tuple(args))));
                        let expr = shared(Expr::Func(
                            elems
                                .iter()
                                .enumerate()
                                .map(|(i, _)| format!("arg{}", i))
                                .collect(),
                            body,
                            None,
                        ));
                        env.borrow_mut().extend(ctor, expr);
                    }
                    _ => {
                        env.borrow_mut().extend(
                            ctor,
                            shared(Expr::Func(
                                vec!["data".to_string()],
                                shared(Expr::TaggedVariant(
                                    ctor.clone(),
                                    shared(Expr::Var("data".to_string())),
                                )),
                                None,
                            )),
                        );
                    }
                }
            }
        }
    }
    for (name, struct_def) in inf_ctx.struct_defs.iter() {
        let mut struct_val = HashMap::new();
        for field in struct_def.fields.iter() {
            struct_val.insert(field.name.clone(), shared(Expr::Var(field.name.clone())));
        }
        env.borrow_mut().extend(
            name,
            shared(Expr::Func(
                struct_def.fields.iter().map(|f| f.name.clone()).collect(),
                shared(Expr::Struct(name.clone(), shared(struct_val))),
                None,
            )),
        );
    }

    env
}

pub(crate) type OverloadedFuncMap = HashMap<(Identifier, TypeMonomorphized), Shared<Expr>>;

pub struct Interpreter {
    program_expr: Shared<Expr>,
    env: Rc<RefCell<Environment>>,
    overloaded_func_map: OverloadedFuncMap,
    error: Option<InterpretErr>,
}

pub enum InterpreterStatus {
    OutOfSteps,
    Finished,
    Error(String),
    Effect(EffectCode, Vec<Shared<Expr>>),
}

impl Interpreter {
    pub(crate) fn new(
        overloaded_func_map: OverloadedFuncMap,
        program_expr: Shared<Expr>,
        env: Rc<RefCell<Environment>>,
    ) -> Self {
        Interpreter {
            program_expr,
            env,
            overloaded_func_map,
            error: None,
        }
    }

    pub fn is_finished(&self) -> bool {
        is_val(&self.program_expr) || self.error.is_some()
    }

    pub fn get_val(&self) -> Option<Shared<Expr>> {
        if self.is_finished() {
            Some(self.program_expr.clone())
        } else {
            None
        }
    }

    pub fn run(&mut self, steps: i32, effect_result: Option<Shared<Expr>>) -> InterpreterStatus {
        let result = interpret(
            self.program_expr.clone(),
            self.env.clone(),
            &self.overloaded_func_map,
            steps,
            &effect_result,
        );
        match result {
            Ok(InterpretOk {
                expr,
                steps: _,
                effect,
                new_env,
            }) => {
                self.program_expr = expr;
                self.env = new_env;
                if let Some(effect) = effect {
                    return InterpreterStatus::Effect(effect.0, effect.1);
                }
                if is_val(&self.program_expr) {
                    return InterpreterStatus::Finished;
                }
                InterpreterStatus::OutOfSteps
            }
            Err(err) => InterpreterStatus::Error(err.message),
        }
    }
}

#[derive(Debug)]
struct InterpretOk {
    expr: Shared<Expr>,
    steps: i32,
    effect: Option<(EffectCode, Vec<Shared<Expr>>)>,
    new_env: Rc<RefCell<Environment>>,
}

#[derive(Debug)]
struct InterpretErr {
    // TODO: add location (line and column) of error
    message: String,
}

fn interpret(
    expr: Shared<Expr>,
    env: Rc<RefCell<Environment>>,
    overloaded_func_map: &OverloadedFuncMap,
    steps: i32,
    input: &Option<Shared<Expr>>,
) -> Result<InterpretOk, InterpretErr> {
    match &*expr.borrow() {
        Var(id) => {
            let result = env.borrow_mut().lookup(id);
            match result {
                None => Err(InterpretErr {
                    message: format!("No value for variable with id: {}", id),
                }),
                Some(val) => Ok(InterpretOk {
                    expr: val,
                    steps,
                    effect: None,
                    new_env: env,
                }),
            }
        }
        VarOverloaded(id, instance) => {
            let result = overloaded_func_map.get(&(id.clone(), instance.clone()));
            match result {
                None => Err(InterpretErr {
                    message: format!("No value for variable with id: {}", id),
                }),
                Some(val) => Ok(InterpretOk {
                    expr: val.clone(),
                    steps,
                    effect: None,
                    new_env: env,
                }),
            }
        }
        Unit | Int(_) | Float(_) | Bool(_) | Str(_) | Func(_, _, Some(_)) | Array(_) => {
            Ok(InterpretOk {
                expr: expr.clone(),
                steps,
                effect: None,
                new_env: env,
            })
        }
        Func(id, body, None) => {
            let closure = shared(Environment::new(Some(env.clone())));
            Ok(InterpretOk {
                expr: shared(Func(id.clone(), body.clone(), Some(closure))),
                steps,
                effect: None,
                new_env: env,
            })
        }
        Tuple(exprs) => {
            let mut new_exprs = exprs.clone();
            for (i, expr) in exprs.iter().enumerate() {
                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                new_exprs[i] = expr;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Tuple(new_exprs)),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            Ok(InterpretOk {
                expr: shared(Tuple(new_exprs)),
                steps,
                effect: None,
                new_env: env,
            })
        }

        TaggedVariant(tag, expr) => {
            let InterpretOk {
                expr,
                steps,
                effect,
                new_env,
            } = interpret(
                expr.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(TaggedVariant(tag.clone(), expr)),
                    steps,
                    effect,
                    new_env,
                });
            }
            Ok(InterpretOk {
                expr: shared(TaggedVariant(tag.clone(), expr)),
                steps,
                effect: None,
                new_env: env,
            })
        }
        Struct(name, fields) => {
            let fields_copy = fields.borrow().clone();
            let keys = fields_copy.keys().cloned().collect::<Vec<String>>();
            for key in keys {
                let val = fields_copy.get(&key).unwrap();
                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    val.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                fields.borrow_mut().insert(key, expr);
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Struct(name.clone(), fields.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            Ok(InterpretOk {
                expr: shared(Struct(name.clone(), fields.clone())),
                steps,
                effect: None,
                new_env: env,
            })
        }
        FieldAccess(accessed, field) => {
            let InterpretOk {
                expr: accessed,
                steps,
                effect,
                new_env,
            } = interpret(
                accessed.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(FieldAccess(accessed, field.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let accessed = accessed.borrow();
            match &*accessed {
                Struct(_, fields) => match fields.borrow().get(field) {
                    Some(expr) => Ok(InterpretOk {
                        expr: expr.clone(),
                        steps,
                        effect: None,
                        new_env,
                    }),
                    None => Err(InterpretErr {
                        message: format!("No field with name: {}", field),
                    }),
                },
                _ => Err(InterpretErr {
                    message: "Field access on non-struct".to_string(),
                }),
            }
        }
        IndexAccess(accessed, index) => {
            let InterpretOk {
                expr: accessed,
                steps,
                effect,
                new_env,
            } = interpret(
                accessed.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(IndexAccess(accessed, index.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let InterpretOk {
                expr: index,
                steps,
                effect,
                new_env,
            } = interpret(
                index.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(IndexAccess(accessed, index.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let Expr::Array(inner) = &*accessed.borrow() else {
                return Err(InterpretErr {
                    message: "Tried to index into non-array".to_string(),
                });
            };
            let Expr::Int(n) = &*index.borrow() else {
                return Err(InterpretErr {
                    message: "Index into array must be an integer".to_string(),
                });
            };
            if *n < 0 || *n as usize >= inner.len() {
                return Err(InterpretErr {
                    message: format!("Index out of bounds: {}", n),
                });
            }
            Ok(InterpretOk {
                expr: inner[*n as usize].clone(),
                steps,
                effect: None,
                new_env,
            })
        }
        BinOp(expr1, op, expr2) => {
            let InterpretOk {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(
                expr1.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(BinOp(expr1, *op, expr2.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let InterpretOk {
                expr: expr2,
                steps,
                effect,
                new_env,
            } = interpret(
                expr2.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                input,
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(BinOp(expr1, *op, expr2)),
                    steps,
                    effect,
                    new_env,
                });
            }
            let val = perform_op(expr1, *op, expr2)?;
            let steps = steps - 1;
            Ok(InterpretOk {
                expr: val,
                steps,
                effect: None,
                new_env: env,
            })
        }
        Let(pat, expr1, expr2) => match &*pat.clone() {
            Pat::TaggedVariant(..)
            | Pat::Unit
            | Pat::Int(_)
            | Pat::Float(_)
            | Pat::Bool(_)
            | Pat::Str(_) => Err(InterpretErr {
                message: "Pattern in let is a value, not a variable!".to_string(),
            }),
            Pat::Wildcard => {
                let InterpretOk {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr1.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }

                let new_env = shared(Environment::new(Some(env.clone())));

                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(expr2.clone(), new_env, overloaded_func_map, steps, input)?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    });
                }
                Ok(InterpretOk {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                })
            }
            Pat::Var(id) => {
                let InterpretOk {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr1.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }

                // Letrec: this code is confusing, and has circular references, sorry :(
                let (expr1, closure) = match &*expr1.borrow() {
                    // TODO: need to use weak reference?
                    //      may be a memory leak because closure has ref to new_env, but new_env contains ref to the val/Func()
                    //      ... which reference needs to be weak??

                    // letrec
                    Func(args, body, Some(closure)) => (
                        shared(Func(args.clone(), body.clone(), Some(closure.clone()))),
                        Some(closure.clone()),
                    ),
                    // letrec
                    Func(args, body, None) => {
                        let closure = shared(Environment::new(Some(env.clone())));
                        (
                            shared(Func(args.clone(), body.clone(), Some(closure.clone()))),
                            Some(closure),
                        )
                    }
                    _ => (expr1.clone(), None),
                };
                if let Some(closure) = closure {
                    closure.borrow_mut().extend(id, expr1.clone());
                }

                let new_env = shared(Environment::new(Some(env.clone())));
                new_env.borrow_mut().extend(id, expr1);

                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(expr2.clone(), new_env, overloaded_func_map, steps, input)?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    });
                }
                Ok(InterpretOk {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                })
            }
            Pat::Tuple(_pats) => {
                let InterpretOk {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr1.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let new_env = shared(Environment::new(Some(env.clone())));
                populate_env(new_env.clone(), pat.clone(), expr1);
                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(expr2.clone(), new_env, overloaded_func_map, steps, input)?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    });
                }
                Ok(InterpretOk {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                })
            }
        },
        Set(assignee, expr1, expr2) => match &*assignee.clone() {
            PlaceExpr::FieldAccess(accessed, field_name) => {
                let InterpretOk {
                    expr: accessed,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    accessed.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Set(
                            Rc::new(PlaceExpr::FieldAccess(accessed, field_name.clone())),
                            expr1.clone(),
                            expr2.clone(),
                        )),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let InterpretOk {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr1.clone(),
                    new_env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Set(
                            Rc::new(PlaceExpr::FieldAccess(accessed, field_name.clone())),
                            expr1.clone(),
                            expr2.clone(),
                        )),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let Expr::Struct(_, fields) = &*accessed.borrow() else {
                    return Err(InterpretErr {
                        message: "Cannot get field from non-struct".to_string(),
                    });
                };
                fields
                    .borrow_mut()
                    .insert(field_name.clone(), expr1.clone());

                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr2.clone(),
                    new_env.clone(),
                    overloaded_func_map,
                    steps,
                    input,
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    });
                }
                Ok(InterpretOk {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                })
            }
            PlaceExpr::IndexAccess(accessed, index) => {
                let InterpretOk {
                    expr: accessed,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    accessed.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Set(
                            Rc::new(PlaceExpr::IndexAccess(accessed, index.clone())),
                            expr1.clone(),
                            expr2.clone(),
                        )),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let InterpretOk {
                    expr: index,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    index.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Set(
                            Rc::new(PlaceExpr::IndexAccess(accessed, index.clone())),
                            expr1.clone(),
                            expr2.clone(),
                        )),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let InterpretOk {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr1.clone(),
                    new_env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Set(
                            Rc::new(PlaceExpr::IndexAccess(accessed, index.clone())),
                            expr1.clone(),
                            expr2.clone(),
                        )),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let Expr::Array(inner) = &mut *accessed.borrow_mut() else {
                    return Err(InterpretErr {
                        message: "Tried to index into non-array".to_string(),
                    });
                };
                let Expr::Int(n) = &*index.borrow() else {
                    return Err(InterpretErr {
                        message: "Index into array must be an integer".to_string(),
                    });
                };
                if *n < 0 || *n as usize >= inner.len() {
                    return Err(InterpretErr {
                        message: format!("Index out of bounds: {}", n),
                    });
                }
                inner[*n as usize] = expr1.clone();

                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr2.clone(),
                    new_env.clone(),
                    overloaded_func_map,
                    steps,
                    input,
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    });
                }
                Ok(InterpretOk {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                })
            }
            PlaceExpr::Var(id) => {
                let InterpretOk {
                    expr: expr1,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    expr1.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(Set(assignee.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }

                env.borrow_mut().replace(id, expr1);

                let InterpretOk {
                    expr,
                    steps,
                    effect,
                    new_env,
                } = interpret(expr2.clone(), new_env, overloaded_func_map, steps, input)?;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    });
                }
                Ok(InterpretOk {
                    expr,
                    steps,
                    effect: None,
                    new_env: env,
                })
            }
        },
        FuncAp(expr1, args, funcapp_env) => {
            let mut new_args = args.clone();
            for (i, arg) in args.iter().enumerate() {
                let InterpretOk {
                    expr: arg,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    arg.clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                new_args[i] = arg;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(FuncAp(expr1.clone(), new_args.clone(), funcapp_env.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            let InterpretOk {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(
                expr1.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(FuncAp(expr1, args.clone(), funcapp_env.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let expr1 = expr1.borrow();
            let (ids, body, closure) = match &*expr1 {
                Func(id, body, closure) => match closure {
                    None => (id, body, shared(Environment::new(Some(env.clone())))),
                    Some(closure) => (id, body, closure.clone()),
                },
                _ => {
                    return Err(InterpretErr {
                        message: format!("not a function {:#?}", expr1),
                    })
                }
            };

            let funcapp_env = match funcapp_env {
                Some(funcapp_env) => funcapp_env.clone(),
                None => {
                    let funcapp_env = shared(Environment::new(Some(closure.clone())));
                    for (i, id) in ids.iter().enumerate() {
                        funcapp_env.borrow_mut().extend(id, new_args[i].clone());
                    }
                    funcapp_env
                }
            };

            let InterpretOk {
                expr: body,
                steps,
                effect,
                new_env: funcapp_env,
            } = interpret(body.clone(), funcapp_env, overloaded_func_map, steps, input)?;
            // if didn't finish executing for the body of function application, return a FuncApp as the expression field try again next time.
            if effect.is_some() || steps <= 0 {
                let result = Ok(InterpretOk {
                    expr: shared(FuncAp(
                        shared(Func(ids.clone(), body, Some(closure))),
                        new_args,
                        Some(funcapp_env),
                    )),
                    steps,
                    effect,
                    new_env,
                });
                return result;
            }
            Ok(InterpretOk {
                expr: body,
                steps,
                effect,
                new_env: env, // return env to normal
            })
        }
        If(expr1, expr2, expr3) => {
            let InterpretOk {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(
                expr1.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(If(expr1, expr2.clone(), expr3.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let expr1 = expr1.borrow();
            match &*expr1 {
                Bool(true) => {
                    let InterpretOk {
                        expr: expr2,
                        steps,
                        effect,
                        new_env,
                    } = interpret(
                        expr2.clone(),
                        env.clone(),
                        overloaded_func_map,
                        steps,
                        input,
                    )?;
                    if effect.is_some() || steps <= 0 {
                        return Ok(InterpretOk {
                            expr: expr2,
                            steps,
                            effect,
                            new_env,
                        });
                    }
                    let steps = steps - 1;
                    Ok(InterpretOk {
                        expr: expr2,
                        steps,
                        effect,
                        new_env: env,
                    })
                }
                Bool(false) => {
                    let InterpretOk {
                        expr: expr3,
                        steps,
                        effect,
                        new_env,
                    } = interpret(
                        expr3.clone(),
                        env.clone(),
                        overloaded_func_map,
                        steps,
                        input,
                    )?;
                    if effect.is_some() || steps <= 0 {
                        return Ok(InterpretOk {
                            expr: expr3,
                            steps,
                            effect,
                            new_env,
                        });
                    }
                    let steps = steps - 1;
                    Ok(InterpretOk {
                        expr: expr3,
                        steps,
                        effect,
                        new_env: env,
                    })
                }
                _ => Err(InterpretErr {
                    message: format!(
                        "If expression clause did not evaluate to a bool: {:#?}",
                        expr1
                    ),
                }),
            }
        }
        WhileLoop(cond, original_cond, body, original_body) => {
            let InterpretOk {
                expr: cond,
                steps,
                effect,
                new_env,
            } = interpret(
                cond.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(WhileLoop(
                        cond,
                        original_cond.clone(),
                        body.clone(),
                        original_body.clone(),
                    )),
                    steps,
                    effect,
                    new_env,
                });
            }
            let cond_is_true = *cond.borrow() == Expr::Bool(true);
            if !cond_is_true {
                return Ok(InterpretOk {
                    expr: shared(Expr::Unit),
                    steps,
                    effect,
                    new_env,
                });
            }

            let InterpretOk {
                expr: new_body,
                steps,
                effect,
                new_env,
            } = interpret(
                body.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(WhileLoop(
                        cond,
                        original_cond.clone(),
                        new_body.clone(),
                        original_body.clone(),
                    )),
                    steps,
                    effect,
                    new_env,
                });
            }
            let steps = steps - 1;
            interpret(
                shared(WhileLoop(
                    original_cond.clone(),
                    original_cond.clone(),
                    original_body.clone(),
                    original_body.clone(),
                )),
                env,
                overloaded_func_map,
                steps,
                input,
            )
        }
        Match(expr1, cases) => {
            let InterpretOk {
                expr: expr1,
                steps,
                effect,
                new_env,
            } = interpret(
                expr1.clone(),
                env.clone(),
                overloaded_func_map,
                steps,
                &input.clone(),
            )?;
            if effect.is_some() || steps <= 0 {
                return Ok(InterpretOk {
                    expr: shared(Match(expr1, cases.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            for (pat, expr) in cases {
                let new_env = shared(Environment::new(Some(env.clone())));
                if match_pattern(pat.clone(), expr1.clone(), new_env.clone()) {
                    let InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env,
                    } = interpret(expr.clone(), new_env, overloaded_func_map, steps, input)?;
                    if effect.is_some() || steps <= 0 {
                        return Ok(InterpretOk {
                            expr,
                            steps,
                            effect,
                            new_env,
                        });
                    }
                    let steps = steps - 1;
                    return Ok(InterpretOk {
                        expr,
                        steps,
                        effect,
                        new_env: env,
                    });
                }
            }
            Err(InterpretErr {
                message: "no match found".to_string(),
            })
        }
        EffectAp(effect_enum, args) => {
            let mut args = args.to_vec();
            for i in 0..args.len() {
                let InterpretOk {
                    expr: arg,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    args[i].clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                args[i] = arg;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(EffectAp(*effect_enum, args.to_vec())),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            let steps = steps - 1;
            Ok(InterpretOk {
                expr: shared(ConsumedEffect),
                steps,
                effect: Some((*effect_enum, args.to_vec())),
                new_env: env,
            })
        }
        BuiltinAp(builtin, args) => {
            let mut args = args.to_vec();
            for i in 0..args.len() {
                let InterpretOk {
                    expr: arg,
                    steps,
                    effect,
                    new_env,
                } = interpret(
                    args[i].clone(),
                    env.clone(),
                    overloaded_func_map,
                    steps,
                    &input.clone(),
                )?;
                args[i] = arg;
                if effect.is_some() || steps <= 0 {
                    return Ok(InterpretOk {
                        expr: shared(BuiltinAp(*builtin, args.to_vec())),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            let steps = steps - 1;
            let result = handle_builtin(*builtin, args.to_vec())?;
            Ok(InterpretOk {
                expr: result,
                steps,
                effect: None,
                new_env: env,
            })
        }
        ConsumedEffect => match input {
            None => Err(InterpretErr {
                message: "no input to substitute for ConsumedEffect".to_string(),
            }),
            Some(input) => Ok(InterpretOk {
                expr: input.clone(),
                steps,
                effect: None,
                new_env: env,
            }), // Input::Cin(string) => InterpretOk {
                //     expr: shared(Str(string.to_string())),
                //     steps,
                //     effect: None,
                //     new_env: env,
                // },
        },
    }
}

fn match_pattern(pat: Rc<Pat>, expr: Shared<Expr>, env: Rc<RefCell<Environment>>) -> bool {
    match (&*pat, &*expr.borrow()) {
        (Pat::Wildcard, _) => true,
        (Pat::Unit, Unit) => true,
        (Pat::Bool(b1), Bool(b2)) => b1 == b2,
        (Pat::Int(i1), Int(i2)) => i1 == i2,
        (Pat::Str(s1), Str(s2)) => s1 == s2,
        (Pat::TaggedVariant(ptag, pdata), TaggedVariant(etag, edata)) => {
            let pdata = pdata.clone().unwrap_or(Rc::new(Pat::Unit));
            ptag == etag && match_pattern(pdata, edata.clone(), env)
        }
        (Pat::Var(id), _) => {
            env.borrow_mut().extend(id, expr.clone());
            true
        }
        (Pat::Tuple(pats), Tuple(exprs)) if pats.len() == exprs.len() => {
            for (pat, expr) in pats.iter().zip(exprs.iter()) {
                if !match_pattern(pat.clone(), expr.clone(), env.clone()) {
                    return false;
                }
            }
            true
        }
        _ => false,
    }
}

fn populate_env(env: Rc<RefCell<Environment>>, pat: Rc<Pat>, expr: Shared<Expr>) {
    match (&*pat, &*expr.borrow()) {
        (Pat::Var(id), _) => env.borrow_mut().extend(id, expr.clone()),
        (Pat::Tuple(pats), Tuple(exprs)) if pats.len() == exprs.len() => {
            for (pat, expr) in pats.iter().zip(exprs.iter()) {
                populate_env(env.clone(), pat.clone(), expr.clone());
            }
        }
        _ => panic!("pattern and expression do not match"),
    }
}

fn handle_builtin(builtin: Builtin, args: Vec<Shared<Expr>>) -> Result<Shared<Expr>, InterpretErr> {
    match builtin {
        Builtin::IntToString => {
            let arg = args[0].borrow();
            match &*arg {
                Int(i) => Ok(shared(Str(i.to_string()))),
                _ => Err(InterpretErr {
                    message: "IntToString expects an int".to_string(),
                }),
            }
        }
        Builtin::FloatToString => {
            let arg = args[0].borrow();
            match &*arg {
                Float(f) => Ok(shared(Str(f.to_string()))),
                _ => Err(InterpretErr {
                    message: "FloatToString expects a float".to_string(),
                }),
            }
        }
        Builtin::IntToFloat => {
            let arg = args[0].borrow();
            match &*arg {
                Int(i) => Ok(shared(Float(*i as f64))),
                _ => Err(InterpretErr {
                    message: "IntToFloat expects an int".to_string(),
                }),
            }
        }
        Builtin::RoundFloatToInt => {
            let arg = args[0].borrow();
            match &*arg {
                Float(f) => Ok(shared(Int(f.round() as i64))),
                _ => Err(InterpretErr {
                    message: "RoundFloatToInt expects a float".to_string(),
                }),
            }
        }
        Builtin::AppendStrings => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Str(s1), Str(s2)) => Ok(shared(Str(s1.to_owned() + s2))),
                _ => Err(InterpretErr {
                    message: "AppendStrings expects two strings".to_string(),
                }),
            }
        }
        Builtin::EqualsInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(i1), Int(i2)) => Ok(shared(Bool(i1 == i2))),
                _ => Err(InterpretErr {
                    message: "EqualsInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::EqualsString => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Str(s1), Str(s2)) => Ok(shared(Bool(s1 == s2))),
                _ => Err(InterpretErr {
                    message: "EqualsString expects two strings".to_string(),
                }),
            }
        }
        Builtin::AddInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(shared(Int(s1 + s2))),
                _ => Err(InterpretErr {
                    message: "AddInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::MinusInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(shared(Int(s1 - s2))),
                _ => Err(InterpretErr {
                    message: "MinusInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::MultiplyInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(shared(Int(s1 * s2))),
                _ => Err(InterpretErr {
                    message: "MultiplyInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::DivideInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(shared(Int(s1 / s2))),
                _ => Err(InterpretErr {
                    message: "DivideInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::PowInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(shared(Int(s1.pow(i64::try_into(*s2).unwrap())))),
                _ => Err(InterpretErr {
                    message: "PowInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::LessThanInt => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(shared(Bool(s1 < s2))),
                _ => Err(InterpretErr {
                    message: "LessThanInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::AddFloat => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(shared(Float(s1 + s2))),
                _ => Err(InterpretErr {
                    message: "AddFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::MinusFloat => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(shared(Float(s1 - s2))),
                _ => Err(InterpretErr {
                    message: "MinusFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::MultiplyFloat => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(shared(Float(s1 * s2))),
                _ => Err(InterpretErr {
                    message: "MultiplyFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::DivideFloat => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(shared(Float(s1 / s2))),
                _ => Err(InterpretErr {
                    message: "DivideFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::PowFloat => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(shared(Float(s1.powf(*s2)))),
                _ => Err(InterpretErr {
                    message: "PowFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::SqrtFloat => {
            let arg = args[0].borrow();
            match &*arg {
                Float(s1) => Ok(shared(Float(s1.sqrt()))),
                _ => Err(InterpretErr {
                    message: "SqrtFloat expects one float".to_string(),
                }),
            }
        }
        Builtin::LessThanFloat => {
            let arg1 = args[0].borrow();
            let arg2 = args[1].borrow();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(shared(Bool(s1 < s2))),
                _ => Err(InterpretErr {
                    message: "LessThanFloat expects two floats".to_string(),
                }),
            }
        }
    }
}

fn perform_op(
    val1: Shared<Expr>,
    op: BinOpcode,
    val2: Shared<Expr>,
) -> Result<Shared<Expr>, InterpretErr> {
    match op {
        Add | Subtract | Multiply | Divide | Pow | Equals => Err(InterpretErr {
            message: format!("{:?} operator was not overloaded properly!", op),
        }),
        Mod => match (&*val1.borrow(), &*val2.borrow()) {
            (Int(i1), Int(i2)) => Ok(shared(Int(i1 % i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of Mod are not ints".to_string(),
            }),
        },
        GreaterThan => match (&*val1.borrow(), &*val2.borrow()) {
            (Int(i1), Int(i2)) => Ok(shared(Bool(i1 > i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of GreaterThan are not ints".to_string(),
            }),
        },
        GreaterThanOrEqual => match (&*val1.borrow(), &*val2.borrow()) {
            (Int(i1), Int(i2)) => Ok(shared(Bool(i1 >= i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of GreaterThanOrEqual are not ints".to_string(),
            }),
        },
        LessThan => match (&*val1.borrow(), &*val2.borrow()) {
            (Int(i1), Int(i2)) => Ok(shared(Bool(i1 < i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of LessThan are not ints".to_string(),
            }),
        },
        LessThanOrEqual => match (&*val1.borrow(), &*val2.borrow()) {
            (Int(i1), Int(i2)) => Ok(shared(Bool(i1 <= i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of LessThanOrEqual are not ints".to_string(),
            }),
        },
        And => match (&*val1.borrow(), &*val2.borrow()) {
            (Bool(b1), Bool(b2)) => Ok(shared(Bool(*b1 && *b2))),
            _ => Err(InterpretErr {
                message: "one or more operands of And are not bools".to_string(),
            }),
        },
        Or => match (&*val1.borrow(), &*val2.borrow()) {
            (Bool(b1), Bool(b2)) => Ok(shared(Bool(*b1 || *b2))),
            _ => Err(InterpretErr {
                message: "one or more operands of Or are not bools".to_string(),
            }),
        },
        Concat => match (&*val1.borrow(), &*val2.borrow()) {
            (Str(s1), Str(s2)) => Ok(shared(Str(s1.to_owned() + s2))),
            _ => Err(InterpretErr {
                message: "one or more operands of Concat are not strings".to_string(),
            }),
        },
    }
}
