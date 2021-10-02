extern crate pest;
#[macro_use]
extern crate pest_derive;

pub mod parser;

use parser::parser::do_stuff;

fn main() {
    println!("Hello world");

    do_stuff();
}