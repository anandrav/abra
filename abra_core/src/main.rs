#[macro_use] 
extern crate lalrpop_util;

mod parsetree;
mod parser;

fn main() {
    println!("Hello world");

    parser::do_stuff();
}