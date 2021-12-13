#[macro_use] 
extern crate lalrpop_util;

mod operators;
mod types;
mod parser;
mod parse_tree;
mod interpreter;

fn main() {
    println!("Hello world");

    let expr = parser::do_stuff();
    let val = interpreter::eval(expr, &interpreter::Context::empty());

    println!("Expr evaluated to val: {:#?}", val);
}