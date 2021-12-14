#[macro_use]
extern crate lalrpop_util;

mod interpreter;
mod operators;
mod parse_tree;
mod parser;
mod side_effects;
mod type_checker;
mod typed_tree;
mod types;

fn main() {
    println!("Hello world");

    let parsed_expr = parser::do_stuff();
    let typed_expr = type_checker::strip_options_expr(parsed_expr.clone());
    let val = interpreter::eval(typed_expr, &interpreter::Effects::empty());

    println!("Expr evaluated to val: {:#?}", val);
}
