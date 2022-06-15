#[macro_use]
extern crate lalrpop_util;
extern crate regex;

use std::cell::RefCell;
use std::fmt;
use std::rc::Rc;

pub mod edit_tree;

mod environment;
mod eval_tree;
mod interpreter;
mod operators;
mod parse_tree;
mod parser;
mod side_effects;
mod translate;
mod type_checker;
mod typed_tree;
mod types;

pub fn blahblah() -> String {
    let mut output = String::new();

    println!("abra_core::main()\n");
    fmt::write(&mut output, format_args!("abra_core::main()\n"))
        .expect("Error occurred while trying to write in String");

    let mut env = Rc::new(RefCell::new(environment::Environment::new(None)));
    env.borrow_mut().extend(
        &String::from("print"),
        Rc::new(eval_tree::Expr::Func(
            String::from("str"),
            Rc::new(eval_tree::Expr::EffectAp(
                side_effects::Effect::Print,
                vec![Rc::new(eval_tree::Expr::Var(String::from("str")))],
            )),
            None,
        )),
    );
    // Rc::new(eval_tree::Expr::Effect(side_effects::Effect::Print))
    // TODO anand: you were last here

    let source = r#"
print("hello world");
print("I am Anand");
print("bleep bloop")"#;
    let source = "
    let f_helper : int -> int -> int -> int = func (n: int, x: int, y: int) -> int {
        if n == 0 {
            x
        } else {
            f_helper(n-1,y,x+y)
        }
    }
    in let fibonacci : int -> int = func (n: int) -> int {
        f_helper(n,0,1)
    }
    in fibonacci(10)
    ";
    println!("{}", source);
    fmt::write(&mut output, format_args!("{}", source))
        .expect("Error occurred while trying to write in String");
    let parsed_expr = parser::parse(&source);
    let typed_expr = type_checker::strip_options_expr(parsed_expr.clone());
    let mut eval_expr = translate::translate_expr(typed_expr);
    // let eval_expr = interpreter::eval(
    //     eval_expr,
    //     Rc::new(RefCell::new(environment::Environment::new(None))),
    // );
    let mut next_input = None;
    println!("================================================================================");
    fmt::write(
        &mut output,
        format_args!(
            "================================================================================"
        ),
    )
    .expect("Error occurred while trying to write in String");
    loop {
        let result = interpreter::interpret(eval_expr, env.clone(), 1, &next_input);
        eval_expr = result.expr;
        env = result.new_env;
        next_input = match result.effect {
            None => None,
            Some((effect, args)) => Some(side_effects::handle_effect(&effect, &args)),
        };
        match (&next_input, eval_tree::is_val(&eval_expr)) {
            (None, true) => {
                break;
            }
            _ => {
                // println!("Env is: {:#?}", env);
                // println!("Expr is: {:#?}", eval_expr)
            }
        };
    }
    println!("================================================================================");
    fmt::write(
        &mut output,
        format_args!(
            "================================================================================"
        ),
    )
    .expect("Error occurred while trying to write in String");

    println!("Expr evaluated to: {:#?}", eval_expr);
    fmt::write(
        &mut output,
        format_args!("Expr evaluated to: {:#?}", eval_expr),
    )
    .expect("Error occurred while trying to write in String");

    output
}
