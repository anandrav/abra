lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

pub fn do_stuff() {
    // let expr = abra_grammar::ExprParser::new()
    //     .parse("22 * 44 + 66; 85")
    //     .unwrap();

    // let to_parse = "(2 + 3) * 4";
    let to_parse = "let x : int = 2 in (x + x)";
    println!("{}", to_parse);
    let expr = abra_grammar::ExprParser::new()
        .parse(to_parse)
        .unwrap();
    println!("{}", format!("{:#?}", expr));
}