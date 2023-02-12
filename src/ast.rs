use crate::operators::BinOpcode;
// use pest::error::{Error, ErrorVariant, InputLocation::Pos};
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest::Parser;
use pest_derive::Parser;
use std::rc::Rc;
#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

// pub fn parse(source: &str) -> Result<Rc<Expr>, String> {
//     abra_grammar::ExprParser::new()
//         .parse(source)
//         .map_err(|err| err.to_string())
// }

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

// TODO: use fix() method in the future
pub fn get_pairs(source: &str) -> Result<Pairs<Rule>, String> {
    MyParser::parse(Rule::expression, source).map_err(|e| e.to_string())
}

pub fn parse_pat(pair: Pair<Rule>, _pratt: &PrattParser<Rule>) -> Rc<Pat> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::identifier => Rc::new(Pat {
            patkind: Rc::new(PatKind::Var(pair.as_str().to_owned())),
            span,
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}
// TODO: make func args patterns
pub fn parse_func_arg(pair: Pair<Rule>, _pratt: &PrattParser<Rule>) -> FuncArg {
    let _span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_func_arg(pair, _pratt)
        }
        Rule::identifier => (pair.as_str().to_owned(), None),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_stmt(pair: Pair<Rule>, pratt: &PrattParser<Rule>) -> Rc<Stmt> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::let_statement => {
            let pat = parse_pat(inner[0].clone(), pratt);
            let expr = parse_expr_pratt(Pairs::single(inner[1].clone()), pratt);
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::Let(pat, None, expr)),
                span,
            })
        }
        Rule::expression_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), pratt);
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::Expr(expr)),
                span,
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

fn rule_is_of_stmt(rule: &Rule) -> bool {
    matches!(rule, Rule::let_statement | Rule::expression_statement)
}

pub fn parse_expr_term(pair: Pair<Rule>, pratt: &PrattParser<Rule>) -> Rc<Expr> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        /* emitting Pairs for expression and then re-running on its inner pairs is
         * necessary to be able to distinguish its inner pairs from the pairs of an adjacent,
         * but different, expression.
         * For instance, in the expression
         *          if n == 0 { 2 } else { 3 }
         * (n == 0) would be parsed as a Rule::expression, followed by two Rule::block_expressions
         * If 'n' '==' and '0' were not grouped under a Rule::expression, it would be difficult
         * to run the pratt parser on just them.
         */
        Rule::expression => parse_expr_pratt(pair.into_inner(), pratt),
        // All rules listed below should be non-operator expressions
        Rule::block_expression => {
            let inner = pair.into_inner();
            let mut statements: Vec<Rc<Stmt>> = Vec::new();
            let mut expression: Option<Rc<Expr>> = None;
            for pair in inner {
                if rule_is_of_stmt(&pair.as_rule()) {
                    statements.push(parse_stmt(pair, pratt));
                } else {
                    expression = Some(parse_expr_pratt(Pairs::single(pair), pratt));
                }
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Block(statements, expression)),
                span,
            })
        }
        Rule::if_else_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), pratt);
            let e1 = parse_expr_pratt(Pairs::single(inner[1].clone()), pratt);
            let e2 = parse_expr_pratt(Pairs::single(inner[2].clone()), pratt);
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::If(cond, e1, e2)),
                span,
            })
        }
        Rule::func_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let arg1 = parse_func_arg(inner[0].clone(), pratt);
            let mut remaining_args = Vec::new();
            for p in &inner[1..inner.len() - 1] {
                remaining_args.push(parse_func_arg(p.clone(), pratt));
            }
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), pratt);
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Func(arg1, remaining_args, None, body)),
                span,
            })
        }
        Rule::func_call_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let f = parse_expr_pratt(Pairs::single(inner[0].clone()), pratt);
            let arg1 = parse_expr_pratt(Pairs::single(inner[1].clone()), pratt);
            let mut remaining_args = Vec::new();
            for p in &inner[2..] {
                remaining_args.push(parse_expr_pratt(Pairs::single(p.clone()), pratt));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::FuncAp(f, arg1, remaining_args)),
                span,
            })
        }
        Rule::literal_unit => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Unit),
            span,
        }),
        Rule::literal_number => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Int(pair.as_str().parse().unwrap())),
            span,
        }),
        Rule::literal_bool => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Bool(pair.as_str().parse().unwrap())),
            span,
        }),
        Rule::literal_string => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
        }),
        Rule::identifier => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Var(pair.as_str().to_owned())),
            span,
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_expr_pratt(pairs: Pairs<Rule>, pratt: &PrattParser<Rule>) -> Rc<Expr> {
    pratt
        .map_primary(|primary| parse_expr_term(primary, pratt))
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
                Rule::op_eq => BinOpcode::Equals,
                Rule::op_gt => BinOpcode::GreaterThan,
                Rule::op_lt => BinOpcode::LessThan,
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

pub fn parse_or_err(source: &str) -> Result<Rc<Expr>, String> {
    let pairs = get_pairs(source)?;
    // at this point, we know it's syntactically correct,
    // so we figure out operator precedence using the pratt parser
    let pratt = PrattParser::new()
        .op(Op::infix(Rule::op_eq, Assoc::Left))
        .op(Op::infix(Rule::op_lt, Assoc::Left) | Op::infix(Rule::op_gt, Assoc::Left))
        .op(Op::infix(Rule::op_addition, Assoc::Left)
            | Op::infix(Rule::op_subtraction, Assoc::Left))
        .op(Op::infix(Rule::op_multiplication, Assoc::Left)
            | Op::infix(Rule::op_division, Assoc::Left));
    Ok(parse_expr_pratt(pairs, &pratt))
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
    // Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>, Option<Rc<Expr>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, Vec<Rc<Expr>>),
}

// pub type MatchArm = (Rc<Pat>, Rc<Expr>);

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

#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    Unknown,
    Unit,
    Int,
    Bool,
    String,
    Arrow(Rc<Type>, Rc<Type>),
}
