#[macro_use] 
extern crate lalrpop_util;

mod parse_tree;
mod parser;
mod operators;
mod types;

fn main() {
    println!("Hello world");

    parser::do_stuff();
}