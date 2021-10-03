#[macro_use] 
extern crate lalrpop_util;

mod ast;
mod parser;

fn main() {
    println!("Hello world");

    parser::do_stuff();
}