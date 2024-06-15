use crate::environment::Environment;
use crate::eval_tree::Expr::*;
use crate::eval_tree::*;
use crate::operators::BinOpcode::*;
use crate::operators::*;

use crate::side_effects::*;
use crate::statics::InferenceContext;
use crate::statics::SolvedType;
use crate::statics::TypeMonomorphized;
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
        Rc::new(Expr::Str(String::from("\n"))),
    );
    for (idx, eff) in Effects::enumerate().iter().enumerate() {
        let (arg_types, _ret_type) = eff.type_signature();
        let mut args = vec![];
        for (i, _) in arg_types.iter().enumerate() {
            args.push(format!("arg{}", i));
        }
        let body = Rc::new(Expr::EffectAp(
            idx.try_into().unwrap(),
            arg_types
                .iter()
                .enumerate()
                .map(|(i, _)| Rc::new(Expr::Var(format!("arg{}", i))))
                .collect(),
        ));
        let expr = Rc::new(Expr::Func(args, body, None));
        env.borrow_mut().extend(&eff.function_name(), expr);
    }
    env.borrow_mut().extend(
        &String::from("equals_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::EqualsInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("equals_string"),
        Rc::new(Expr::Func(
            vec![String::from("s1"), String::from("s2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::EqualsString,
                vec![
                    Rc::new(Expr::Var(String::from("s1"))),
                    Rc::new(Expr::Var(String::from("s2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("int_to_string"),
        Rc::new(Expr::Func(
            vec![String::from("some_int")],
            Rc::new(Expr::BuiltinAp(
                Builtin::IntToString,
                vec![Rc::new(Expr::Var(String::from("some_int")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("float_to_string"),
        Rc::new(Expr::Func(
            vec![String::from("some_float")],
            Rc::new(Expr::BuiltinAp(
                Builtin::FloatToString,
                vec![Rc::new(Expr::Var(String::from("some_float")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("to_float"),
        Rc::new(Expr::Func(
            vec![String::from("some_int")],
            Rc::new(Expr::BuiltinAp(
                Builtin::IntToFloat,
                vec![Rc::new(Expr::Var(String::from("some_int")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("round"),
        Rc::new(Expr::Func(
            vec![String::from("some_float")],
            Rc::new(Expr::BuiltinAp(
                Builtin::RoundFloatToInt,
                vec![Rc::new(Expr::Var(String::from("some_float")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("append_strings"),
        Rc::new(Expr::Func(
            vec![String::from("s1"), String::from("s2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::AppendStrings,
                vec![
                    Rc::new(Expr::Var(String::from("s1"))),
                    Rc::new(Expr::Var(String::from("s2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("add_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::AddInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("minus_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::MinusInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("multiply_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::MultiplyInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("divide_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::DivideInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("pow_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::PowInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("less_than_int"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::LessThanInt,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("add_float"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::AddFloat,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("minus_float"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::MinusFloat,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("multiply_float"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::MultiplyFloat,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("divide_float"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::DivideFloat,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("pow_float"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::PowFloat,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
                ],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("sqrt_float"),
        Rc::new(Expr::Func(
            vec![String::from("f")],
            Rc::new(Expr::BuiltinAp(
                Builtin::SqrtFloat,
                vec![Rc::new(Expr::Var(String::from("f")))],
            )),
            None,
        )),
    );
    env.borrow_mut().extend(
        &String::from("less_than_float"),
        Rc::new(Expr::Func(
            vec![String::from("i1"), String::from("i2")],
            Rc::new(Expr::BuiltinAp(
                Builtin::LessThanFloat,
                vec![
                    Rc::new(Expr::Var(String::from("i1"))),
                    Rc::new(Expr::Var(String::from("i2"))),
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
                    Rc::new(Expr::TaggedVariant(ctor.clone(), Rc::new(Expr::Unit))),
                );
            } else {
                match &variant.data.solution().unwrap() {
                    SolvedType::Tuple(elems) => {
                        let mut args = vec![];
                        for (i, _) in elems.iter().enumerate() {
                            args.push(Rc::new(Expr::Var(format!("arg{}", i))));
                        }
                        let body = Rc::new(Expr::TaggedVariant(
                            ctor.clone(),
                            Rc::new(Expr::Tuple(args)),
                        ));
                        let expr = Rc::new(Expr::Func(
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
                            Rc::new(Expr::Func(
                                vec!["data".to_string()],
                                Rc::new(Expr::TaggedVariant(
                                    ctor.clone(),
                                    Rc::new(Expr::Var("data".to_string())),
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
            struct_val.insert(field.name.clone(), Rc::new(Expr::Var(field.name.clone())));
        }
        env.borrow_mut().extend(
            name,
            Rc::new(Expr::Func(
                struct_def.fields.iter().map(|f| f.name.clone()).collect(),
                Rc::new(Expr::Struct(
                    name.clone(),
                    Rc::new(RefCell::new(struct_val)),
                )),
                None,
            )),
        );
    }

    env
}

pub(crate) type OverloadedFuncMap = HashMap<(Identifier, TypeMonomorphized), Rc<Expr>>;

pub struct Interpreter {
    program_expr: Rc<Expr>,
    env: Rc<RefCell<Environment>>,
    overloaded_func_map: OverloadedFuncMap,
    error: Option<InterpretErr>,
}

pub enum InterpreterStatus {
    OutOfSteps,
    Finished,
    Error(String),
    Effect(EffectCode, Vec<Rc<Expr>>),
}

impl Interpreter {
    pub(crate) fn new(
        overloaded_func_map: OverloadedFuncMap,
        program_expr: Rc<Expr>,
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

    pub fn get_val(&self) -> Option<Rc<Expr>> {
        if self.is_finished() {
            Some(self.program_expr.clone())
        } else {
            None
        }
    }

    pub fn run(&mut self, steps: i32, effect_result: Option<Rc<Expr>>) -> InterpreterStatus {
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
    expr: Rc<Expr>,
    steps: i32,
    effect: Option<(EffectCode, Vec<Rc<Expr>>)>,
    new_env: Rc<RefCell<Environment>>,
}

#[derive(Debug)]
struct InterpretErr {
    // TODO: add location (line and column) of error
    message: String,
}

fn interpret(
    expr: Rc<Expr>,
    env: Rc<RefCell<Environment>>,
    overloaded_func_map: &OverloadedFuncMap,
    steps: i32,
    input: &Option<Rc<Expr>>,
) -> Result<InterpretOk, InterpretErr> {
    match &*expr {
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
            let closure = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
            Ok(InterpretOk {
                expr: Rc::new(Func(id.clone(), body.clone(), Some(closure))),
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
                        expr: Rc::new(Tuple(new_exprs)),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            Ok(InterpretOk {
                expr: Rc::new(Tuple(new_exprs)),
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
                    expr: Rc::new(TaggedVariant(tag.clone(), expr)),
                    steps,
                    effect,
                    new_env,
                });
            }
            Ok(InterpretOk {
                expr: Rc::new(TaggedVariant(tag.clone(), expr)),
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
                        expr: Rc::new(Struct(name.clone(), fields.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            Ok(InterpretOk {
                expr: Rc::new(Struct(name.clone(), fields.clone())),
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
                    expr: Rc::new(FieldAccess(accessed, field.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
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
                    expr: Rc::new(IndexAccess(accessed, index.clone())),
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
                    expr: Rc::new(IndexAccess(accessed, index.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let Expr::Array(inner) = &*accessed else {
                return Err(InterpretErr {
                    message: "Tried to index into non-array".to_string(),
                });
            };
            let Expr::Int(n) = &*index else {
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
                    expr: Rc::new(BinOp(expr1, *op, expr2.clone())),
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
                    expr: Rc::new(BinOp(expr1, *op, expr2)),
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
                        expr: Rc::new(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }

                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));

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
                        expr: Rc::new(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }

                // Letrec: this code is confusing, and has circular references, sorry :(
                let (expr1, closure) = match &*expr1 {
                    // TODO: need to use weak reference?
                    //      may be a memory leak because closure has ref to new_env, but new_env contains ref to the val/Func()
                    //      ... which reference needs to be weak??

                    // letrec
                    Func(args, body, Some(closure)) => (
                        Rc::new(Func(args.clone(), body.clone(), Some(closure.clone()))),
                        Some(closure.clone()),
                    ),
                    // letrec
                    Func(args, body, None) => {
                        let closure = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
                        (
                            Rc::new(Func(args.clone(), body.clone(), Some(closure.clone()))),
                            Some(closure),
                        )
                    }
                    _ => (expr1, None),
                };
                if let Some(closure) = closure {
                    closure.borrow_mut().extend(id, expr1.clone());
                }

                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
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
                        expr: Rc::new(Let(pat.clone(), expr1, expr2.clone())),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
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
                        expr: Rc::new(Set(
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
                        expr: Rc::new(Set(
                            Rc::new(PlaceExpr::FieldAccess(accessed, field_name.clone())),
                            expr1.clone(),
                            expr2.clone(),
                        )),
                        steps,
                        effect,
                        new_env,
                    });
                }
                let Expr::Struct(_, fields) = &*accessed else {
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
                        expr: Rc::new(Set(assignee.clone(), expr1, expr2.clone())),
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
                        expr: Rc::new(FuncAp(expr1.clone(), new_args.clone(), funcapp_env.clone())),
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
                    expr: Rc::new(FuncAp(expr1, args.clone(), funcapp_env.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            let (ids, body, closure) = match &*expr1 {
                Func(id, body, closure) => match closure {
                    None => (
                        id,
                        body,
                        Rc::new(RefCell::new(Environment::new(Some(env.clone())))),
                    ),
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
                    let funcapp_env =
                        Rc::new(RefCell::new(Environment::new(Some(closure.clone()))));
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
                    expr: Rc::new(FuncAp(
                        Rc::new(Func(ids.clone(), body, Some(closure))),
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
                    expr: Rc::new(If(expr1, expr2.clone(), expr3.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
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
                    expr: Rc::new(WhileLoop(
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
            let cond_is_true = *cond == Expr::Bool(true);
            if !cond_is_true {
                return Ok(InterpretOk {
                    expr: Rc::new(Expr::Unit),
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
                    expr: Rc::new(WhileLoop(
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
                Rc::new(WhileLoop(
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
                    expr: Rc::new(Match(expr1, cases.clone())),
                    steps,
                    effect,
                    new_env,
                });
            }
            for (pat, expr) in cases {
                let new_env = Rc::new(RefCell::new(Environment::new(Some(env.clone()))));
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
                        expr: Rc::new(EffectAp(*effect_enum, args.to_vec())),
                        steps,
                        effect,
                        new_env,
                    });
                }
            }
            let steps = steps - 1;
            Ok(InterpretOk {
                expr: Rc::new(ConsumedEffect),
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
                        expr: Rc::new(BuiltinAp(*builtin, args.to_vec())),
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
                //     expr: Rc::new(Str(string.to_string())),
                //     steps,
                //     effect: None,
                //     new_env: env,
                // },
        },
    }
}

fn match_pattern(pat: Rc<Pat>, expr: Rc<Expr>, env: Rc<RefCell<Environment>>) -> bool {
    match (&*pat, &*expr) {
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

fn populate_env(env: Rc<RefCell<Environment>>, pat: Rc<Pat>, expr: Rc<Expr>) {
    match (&*pat, &*expr) {
        (Pat::Var(id), _) => env.borrow_mut().extend(id, expr.clone()),
        (Pat::Tuple(pats), Tuple(exprs)) if pats.len() == exprs.len() => {
            for (pat, expr) in pats.iter().zip(exprs.iter()) {
                populate_env(env.clone(), pat.clone(), expr.clone());
            }
        }
        _ => panic!("pattern and expression do not match"),
    }
}

fn handle_builtin(builtin: Builtin, args: Vec<Rc<Expr>>) -> Result<Rc<Expr>, InterpretErr> {
    match builtin {
        Builtin::IntToString => {
            let arg = args[0].clone();
            match &*arg {
                Int(i) => Ok(Rc::new(Str(i.to_string()))),
                _ => Err(InterpretErr {
                    message: "IntToString expects an int".to_string(),
                }),
            }
        }
        Builtin::FloatToString => {
            let arg = args[0].clone();
            match &*arg {
                Float(f) => Ok(Rc::new(Str(f.to_string()))),
                _ => Err(InterpretErr {
                    message: "FloatToString expects a float".to_string(),
                }),
            }
        }
        Builtin::IntToFloat => {
            let arg = args[0].clone();
            match &*arg {
                Int(i) => Ok(Rc::new(Float(*i as f64))),
                _ => Err(InterpretErr {
                    message: "IntToFloat expects an int".to_string(),
                }),
            }
        }
        Builtin::RoundFloatToInt => {
            let arg = args[0].clone();
            match &*arg {
                Float(f) => Ok(Rc::new(Int(f.round() as i64))),
                _ => Err(InterpretErr {
                    message: "RoundFloatToInt expects a float".to_string(),
                }),
            }
        }
        Builtin::AppendStrings => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Str(s1), Str(s2)) => Ok(Rc::new(Str(s1.to_owned() + s2))),
                _ => Err(InterpretErr {
                    message: "AppendStrings expects two strings".to_string(),
                }),
            }
        }
        Builtin::EqualsInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(i1), Int(i2)) => Ok(Rc::new(Bool(i1 == i2))),
                _ => Err(InterpretErr {
                    message: "EqualsInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::EqualsString => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Str(s1), Str(s2)) => Ok(Rc::new(Bool(s1 == s2))),
                _ => Err(InterpretErr {
                    message: "EqualsString expects two strings".to_string(),
                }),
            }
        }
        Builtin::AddInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(Rc::new(Int(s1 + s2))),
                _ => Err(InterpretErr {
                    message: "AddInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::MinusInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(Rc::new(Int(s1 - s2))),
                _ => Err(InterpretErr {
                    message: "MinusInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::MultiplyInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(Rc::new(Int(s1 * s2))),
                _ => Err(InterpretErr {
                    message: "MultiplyInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::DivideInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(Rc::new(Int(s1 / s2))),
                _ => Err(InterpretErr {
                    message: "DivideInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::PowInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(Rc::new(Int(s1.pow(i64::try_into(*s2).unwrap())))),
                _ => Err(InterpretErr {
                    message: "PowInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::LessThanInt => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Int(s1), Int(s2)) => Ok(Rc::new(Bool(s1 < s2))),
                _ => Err(InterpretErr {
                    message: "LessThanInt expects two ints".to_string(),
                }),
            }
        }
        Builtin::AddFloat => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(Rc::new(Float(s1 + s2))),
                _ => Err(InterpretErr {
                    message: "AddFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::MinusFloat => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(Rc::new(Float(s1 - s2))),
                _ => Err(InterpretErr {
                    message: "MinusFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::MultiplyFloat => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(Rc::new(Float(s1 * s2))),
                _ => Err(InterpretErr {
                    message: "MultiplyFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::DivideFloat => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(Rc::new(Float(s1 / s2))),
                _ => Err(InterpretErr {
                    message: "DivideFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::PowFloat => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(Rc::new(Float(s1.powf(*s2)))),
                _ => Err(InterpretErr {
                    message: "PowFloat expects two floats".to_string(),
                }),
            }
        }
        Builtin::SqrtFloat => {
            let arg = args[0].clone();
            match &*arg {
                Float(s1) => Ok(Rc::new(Float(s1.sqrt()))),
                _ => Err(InterpretErr {
                    message: "SqrtFloat expects one float".to_string(),
                }),
            }
        }
        Builtin::LessThanFloat => {
            let arg1 = args[0].clone();
            let arg2 = args[1].clone();
            match (&*arg1, &*arg2) {
                (Float(s1), Float(s2)) => Ok(Rc::new(Bool(s1 < s2))),
                _ => Err(InterpretErr {
                    message: "LessThanFloat expects two floats".to_string(),
                }),
            }
        }
    }
}

fn perform_op(val1: Rc<Expr>, op: BinOpcode, val2: Rc<Expr>) -> Result<Rc<Expr>, InterpretErr> {
    match op {
        Add | Subtract | Multiply | Divide | Pow | Equals => Err(InterpretErr {
            message: format!("{:?} operator was not overloaded properly!", op),
        }),
        Mod => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Ok(Rc::new(Int(i1 % i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of Mod are not ints".to_string(),
            }),
        },
        GreaterThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Ok(Rc::new(Bool(i1 > i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of GreaterThan are not ints".to_string(),
            }),
        },
        GreaterThanOrEqual => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Ok(Rc::new(Bool(i1 >= i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of GreaterThanOrEqual are not ints".to_string(),
            }),
        },
        LessThan => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Ok(Rc::new(Bool(i1 < i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of LessThan are not ints".to_string(),
            }),
        },
        LessThanOrEqual => match (&*val1, &*val2) {
            (Int(i1), Int(i2)) => Ok(Rc::new(Bool(i1 <= i2))),
            _ => Err(InterpretErr {
                message: "one or more operands of LessThanOrEqual are not ints".to_string(),
            }),
        },
        And => match (&*val1, &*val2) {
            (Bool(b1), Bool(b2)) => Ok(Rc::new(Bool(*b1 && *b2))),
            _ => Err(InterpretErr {
                message: "one or more operands of And are not bools".to_string(),
            }),
        },
        Or => match (&*val1, &*val2) {
            (Bool(b1), Bool(b2)) => Ok(Rc::new(Bool(*b1 || *b2))),
            _ => Err(InterpretErr {
                message: "one or more operands of Or are not bools".to_string(),
            }),
        },
        Concat => match (&*val1, &*val2) {
            (Str(s1), Str(s2)) => Ok(Rc::new(Str(s1.to_owned() + s2))),
            _ => Err(InterpretErr {
                message: "one or more operands of Concat are not strings".to_string(),
            }),
        },
    }
}
