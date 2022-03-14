lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

use parse_tree;
use std::rc::Rc;

pub fn do_stuff() -> Rc<parse_tree::Expr> {
    // let expr = abra_grammar::ExprParser::new()
    //     .parse("22 * 44 + 66; 85")
    //     .unwrap();

    // let to_parse = "(2 + 3) * 4";
    // let to_parse = "if 2 + 2 < 5 == 2 + 2 > 5 { 3 } else { 4 }";
    // Celina's favorite program
    // let to_parse = "let foo : int = 2 in let butt : int = 3 in foo + butt";
    // let to_parse = "let x : () = () in x";
    // let to_parse = "let f: int -> int = func (x: int) -> int { x + 2 } in f(1)";
    // let to_parse =
    //     "let f: int -> int -> int = func (x: int) -> int { func (y: int) -> int { x + y } } in f(3)(4)";
    // let to_parse = "let butt : int = 2 in let butt : int = 3 in butt";
    let to_parse = "
    let f : int -> int = func (x: int) -> int {
        if x == 0 {
            0
        } else {
            if x == 1 {
                1
            } else {
                f(x-1) + f(x-2)
            }
        }
    } in f(10)";

    println!("{}", to_parse);
    let expr = abra_grammar::ExprParser::new().parse(to_parse).unwrap();
    // println!("{}", format!("{:#?}", expr));
    return expr;
}
