lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

use parse_tree;
use std::rc::Rc;

pub fn do_stuff() -> Rc<parse_tree::Expr> {
    // let expr = abra_grammar::ExprParser::new()
    //     .parse("22 * 44 + 66; 85")
    //     .unwrap();

    // let to_parse = "(2 + 3) * 4";
    let to_parse = "if 2 + 2 < 5 == 2 + 2 > 5 { 3 } else { 4 }";
    // let to_parse = "let x : int = 2 in let y : int = 3 in x + y";
    // let to_parse = "let x : () = () in x";
    // let to_parse = "let f = func x -> func y -> x + y in f(3)(4)";
    // let to_parse = "let f = func (x) -> int { func (y: int) -> int { x + y } } in f(3)(4)";
    println!("{}", to_parse);
    let expr = abra_grammar::ExprParser::new().parse(to_parse).unwrap();
    // println!("{}", format!("{:#?}", expr));

    return expr;
}
