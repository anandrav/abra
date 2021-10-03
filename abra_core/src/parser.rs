lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

pub fn do_stuff() {
    // let expr = abra_grammar::ExprParser::new()
    //     .parse("22 * 44 + 66; 85")
    //     .unwrap();
    let expr = abra_grammar::ExprParser::new()
        .parse("(2 + 3) * 4")
        .unwrap();
    println!("{}", format!("{:#?}", expr));
}