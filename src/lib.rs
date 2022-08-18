#[macro_use]
extern crate lalrpop_util;
extern crate regex;
lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

use std::rc::Rc;

mod edit_tree;
mod operators;
mod parse_tree;
mod types;

pub fn parse(to_parse: &str) -> Rc<edit_tree::Expr> {
    let parse_tree = abra_grammar::ExprParser::new().parse(to_parse).unwrap();
    edit_tree::Expr::from(parse_tree)
}
