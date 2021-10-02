use pest::Parser;

#[derive(Parser)]
#[grammar = "parser/grammar.pest"]
struct IdentParser;

pub fn do_stuff() {
    let pairs = IdentParser::parse(Rule::expr, "2+4").unwrap_or_else(|e| panic!("{}", e));

    // print_pairs(&mut pairs);

    // Because ident_list is silent, the iterator will contain idents
    for pair in pairs {
        // A pair is a combination of the rule which matched and a span of input
        println!("Rule:    {:?}", pair.as_rule());
        println!("Span:    {:?}", pair.as_span());
        println!("Text:    {}", pair.as_str());

        let mut inner = pair.into_inner();
        print_inner_pairs(&mut inner);
    }
}

pub fn print_inner_pairs(pairs: &mut pest::iterators::Pairs<Rule>) {
    // A pair can be converted to an iterator of the tokens which make it up:
    for inner_pair in pairs {
        match inner_pair.as_rule() {
            Rule::int => println!("Int:  {}", inner_pair.as_str()),
            Rule::add => println!("Add:  {}", inner_pair.as_str()),
            Rule::term => println!("Term:  {}", inner_pair.as_str()),
            Rule::binop_expr => println!("Binop:  {}", inner_pair.as_str()),
            Rule::parenthesized_expr => println!("Parenthesized:   {}", inner_pair.as_str()),
            Rule::expr => println!("Expr:   {}", inner_pair.as_str()),
            _ => ()
        };

        let mut inner = inner_pair.into_inner();
        print_inner_pairs(&mut inner);
    }
}