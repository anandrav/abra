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
    // let to_parse = "
    // let f : int -> int = func (x: int) -> int {
    //     if x == 0 {
    //         0
    //     } else {
    //         if x == 1 {
    //             1
    //         } else {
    //             f(x-1) + f(x-2)
    //         }
    //     }
    // } in f(10)";
    // let to_parse = "
    // let f_helper : int -> int -> int = func (n: int) -> int { func  (x: int) -> int { func (y: int) -> int {
    //     if n == 0 {
    //         x
    //     } else {
    //         f_helper(n-1)(y)(x+y)
    //     }
    // }}}
    // in let f : int -> int = func (n: int) -> int {
    //     f_helper(n)(0)(1)
    // }
    // let to_parse = "
    // let f : int -> int = func (x: int) -> int {
    //     f(x)
    // } in f(0)";
    let to_parse = "let s : string = \"hello world\" in s";

    println!("{}", to_parse);
    let expr = abra_grammar::ExprParser::new().parse(to_parse).unwrap();
    // println!("{}", format!("{:#?}", expr));
    return expr;
}
