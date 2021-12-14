#[macro_use] 
extern crate lalrpop_util;

mod operators;
mod types;
mod parser;
mod parse_tree;
mod type_checker;
mod typed_tree;
mod interpreter;
mod side_effects;

fn main() {
    println!("Hello world");

    let parsed_expr = parser::do_stuff();
    let typed_expr = type_checker::strip_options_expr(parsed_expr.clone());
    let val = interpreter::eval(typed_expr, &interpreter::Effects::empty());

    println!("Expr evaluated to val: {:#?}", val);
}