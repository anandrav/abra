#[macro_use] 
extern crate lalrpop_util;

mod parse_tree;
mod parser;

fn main() {
    println!("Hello world");

    parser::do_stuff();
}