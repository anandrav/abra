use operators::BinOpcode;
use pest::error::{Error, ErrorVariant, InputLocation::Pos};
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest::Parser;
use pest_derive::Parser;
use std::rc::Rc;
use types::Type;
lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP
#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

pub fn parse(source: &str) -> Result<Rc<Expr>, String> {
    abra_grammar::ExprParser::new()
        .parse(source)
        .map_err(|err| err.to_string())
}

// pub fn fix(s: &str) -> String {
//     // debug_println!("fix: {}", s);
//     if let Err(e) = MyParser::parse(Rule::program, &s) {
//         if let ErrorVariant::ParsingError {
//             positives,
//             negatives,
//         } = e.variant
//         {
//             if positives.contains(&Rule::placeholder) {
//                 let mut s = String::from(s);
//                 if let Pos(p) = e.location {
//                     s.insert_str(p, &Token::Placeholder.to_str());
//                     return fix(&s);
//                 }
//             }
//         }
//         // debug_println!("{:#?}", e);
//         panic!()
//     }
//     s.to_string()
// }

// TODO: fix in the future
pub fn get_pairs(source: &str) -> Pairs<Rule> {
    MyParser::parse(Rule::expression, &source).unwrap_or_else(|e| panic!("{}", e))
}

// pub fn parse_pat(pair: Pair<Rule>) -> Rc<Pat> {
//     match pair {}
// }

pub fn parse_expr(pairs: Pairs<Rule>, pratt: &PrattParser<Rule>) -> Rc<Expr> {
    pratt
        .map_primary(|primary| match primary.as_rule() {
            // Rule::block_expression => {
            //     let pairs = primary.into_inner();
            //     let statements: Vec<_> = pairs
            //         .map(|x| match x.as_rule() {
            //             Rule::let_statement => {
            //                 let inner = x.into_inner();

            //                 let pat = inner.find(|x| x.as_rule() == Rule::pattern).unwrap();
            //                 ();
            //                 Rc::new(Stmt {
            //                     stmtkind: StmtKind::Let(id, e1, e2),
            //                     span: Span::from(x.as_span()),
            //                 })
            //             }
            //             Rule::expression_statement => panic!("expression statement"),
            //             Rule::expression => panic!("just expression"),
            //             _ => panic!("{:#?}", x),
            //         })
            //         .collect();
            //     panic!("make expression now")
            //     // Rc::new(Expr {
            //     //     exprkind: Rc::new(ExprKind::Block(statements, None)),
            //     //     span: Span::from(primary.as_span()),
            //     // })
            // }
            Rule::if_else_expression => {
                let inner = primary.into_inner();
                let e = parse_expr(inner, pratt);
                panic!("{:#?}", e)
            }
            Rule::literal_number => Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Int(primary.as_str().parse().unwrap())),
                span: Span::from(primary.as_span()),
            }),
            Rule::literal_bool => Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Bool(primary.as_str().parse().unwrap())),
                span: Span::from(primary.as_span()),
            }),
            _ => {
                println!("{:#?}", primary.as_rule());
                panic!("heyyy")
            } // Rule::term => primary.as_str().parse().unwrap(),
              // Rule::expr => parse2(primary.into_inner()), // from "(" ~ expr ~ ")"
        })
        // .map_prefix(|op, rhs| match op.as_rule() {
        //     Rule::neg  => -rhs,
        //     _          => unreachable!(),
        // })
        // .map_postfix(|lhs, op| match op.as_rule() {
        //     Rule::fac  => (1..lhs+1).product(),
        //     _          => unreachable!(),
        // })
        .map_infix(|lhs, op, rhs| {
            let opcode = match op.as_rule() {
                Rule::op_addition => BinOpcode::Add,
                Rule::op_subtraction => BinOpcode::Subtract,
                Rule::op_multiplication => BinOpcode::Multiply,
                Rule::op_division => BinOpcode::Divide,
                _ => unreachable!(),
            };
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::BinOp(lhs, opcode, rhs)),
                span: Span::from(op.as_span()),
            })
        })
        .parse(pairs)
}

pub fn parse2(source: &str) -> Rc<Expr> {
    let pairs = get_pairs(source);
    // at this point, we know it's syntactically correct,
    // so we figure out operator precedence using the pratt parser
    let pratt = PrattParser::new()
        .op(Op::infix(Rule::op_addition, Assoc::Left)
            | Op::infix(Rule::op_subtraction, Assoc::Left))
        .op(Op::infix(Rule::op_multiplication, Assoc::Left)
            | Op::infix(Rule::op_division, Assoc::Left));
    parse_expr(pairs, &pratt)
}

#[derive(Debug, PartialEq)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

impl From<pest::Span<'_>> for Span {
    fn from(value: pest::Span) -> Self {
        Span {
            lo: value.start(),
            hi: value.end(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub stmtkind: Rc<StmtKind>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum StmtKind {
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>),
    Expr(Rc<Expr>),
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub exprkind: Rc<ExprKind>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum ExprKind {
    // EmptyHole,
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>, Option<Rc<Expr>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, Vec<Rc<Expr>>),
}

pub type MatchArm = (Rc<Pat>, Rc<Expr>);

#[derive(Debug, PartialEq)]
pub struct Pat {
    pub patkind: Rc<PatKind>,
    pub span: Span,
}

#[derive(Debug, PartialEq)]
pub enum PatKind {
    // EmptyHole,
    Var(Identifier),
    // Unit,
    // Int(i32),
    // Bool(bool),
    // Str(String),
}
