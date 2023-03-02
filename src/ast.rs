use crate::operators::BinOpcode;
// use pest::error::{Error, ErrorVariant, InputLocation::Pos};
use crate::types::*;
use pest::iterators::{Pair, Pairs};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use pest::Parser;
use pest_derive::Parser;
use std::collections::HashMap;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};
#[derive(Parser)]
#[grammar = "grammar.pest"]
struct MyParser;

pub type Identifier = String;
pub type FuncArg = (Rc<Pat>, Option<Rc<Type>>);

pub trait Node {
    fn span(&self) -> Span;
    fn id(&self) -> Id;
    fn children(&self) -> Vec<Rc<dyn Node>>;
}

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub stmtkind: Rc<StmtKind>,
    pub span: Span,
    pub id: Id,
}

impl Node for Stmt {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id.clone()
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.stmtkind {
            StmtKind::Let(pat, _, expr) => vec![pat.clone(), expr.clone()],
            StmtKind::Expr(expr) => vec![expr.clone()],
        }
    }
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
    pub id: Id,
}

impl Node for Expr {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id.clone()
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.exprkind {
            ExprKind::Var(_) => vec![],
            ExprKind::Unit => vec![],
            ExprKind::Int(_) => vec![],
            ExprKind::Bool(_) => vec![],
            ExprKind::Str(_) => vec![],
            ExprKind::Func((arg, _), args, _, body) => {
                let mut children: Vec<Rc<dyn Node>> =
                    vec![arg.clone() as Rc<dyn Node>, body.clone()];
                children.extend(args.iter().map(|(a, _)| a.clone() as Rc<dyn Node>));
                children
            }
            ExprKind::If(cond, then, els) => vec![cond.clone(), then.clone(), els.clone()],
            ExprKind::Block(stmts, expr) => {
                let mut children: Vec<Rc<dyn Node>> = stmts
                    .iter()
                    .map(|s| s.clone() as Rc<dyn Node>)
                    .collect::<Vec<_>>();
                if let Some(expr) = expr {
                    children.push(expr.clone());
                }
                children
            }
            ExprKind::BinOp(lhs, _, rhs) => vec![lhs.clone(), rhs.clone()],
            ExprKind::FuncAp(func, arg, args) => {
                let mut children: Vec<Rc<dyn Node>> = vec![func.clone(), arg.clone()];
                children.extend(args.iter().map(|a| a.clone() as Rc<dyn Node>));
                children
            }
        }
    }
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
    pub id: Id,
}

impl Node for Pat {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id.clone()
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.patkind {
            PatKind::Var(_) => vec![],
        }
    }
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

impl PatKind {
    pub fn get_identifier(&self) -> Identifier {
        match self {
            PatKind::Var(id) => id.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Id {
    pub id: usize,
}

impl Id {
    pub fn new() -> Self {
        static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
}

impl Default for Id {
    fn default() -> Self {
        Id::new()
    }
}

#[derive(Debug, Clone, PartialEq)]
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
        Rule::expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_pat(pair, _pratt)
        }
        Rule::identifier => Rc::new(Pat {
            patkind: Rc::new(PatKind::Var(pair.as_str().to_owned())),
            span,
            id: Id::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}
// TODO: make func args patterns
// pub fn parse_func_arg(pair: Pair<Rule>, _pratt: &PrattParser<Rule>) -> FuncArg {
//     let _span = Span::from(pair.as_span());
//     let rule = pair.as_rule();
//     match rule {
//         Rule::expression => {
//             let inner: Vec<_> = pair.into_inner().collect();
//             let pair = inner.first().unwrap().clone();
//             parse_func_arg(pair, _pratt)
//         }
//         Rule::identifier => (pair.as_str().to_owned(), None),
//         _ => panic!("unreachable rule {:#?}", rule),
//     }
// }
pub fn parse_func_arg(pair: Pair<Rule>, pratt: &PrattParser<Rule>) -> FuncArg {
    (parse_pat(pair, pratt), None)
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
                id: Id::new(),
            })
        }
        Rule::expression_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), pratt);
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::Expr(expr)),
                span,
                id: Id::new(),
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
                id: Id::new(),
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
                id: Id::new(),
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
                id: Id::new(),
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
                id: Id::new(),
            })
        }
        Rule::literal_unit => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Unit),
            span,
            id: Id::new(),
        }),
        Rule::literal_number => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Int(pair.as_str().parse().unwrap())),
            span,
            id: Id::new(),
        }),
        Rule::literal_bool => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Bool(pair.as_str().parse().unwrap())),
            span,
            id: Id::new(),
        }),
        Rule::literal_string => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
            id: Id::new(),
        }),
        Rule::identifier => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Var(pair.as_str().to_owned())),
            span,
            id: Id::new(),
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
                id: Id::new(),
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

pub type NodeMap = HashMap<Id, Rc<dyn Node>>;

pub fn populate_node_map(node_map: &mut NodeMap, node: &Rc<dyn Node>) {
    node_map.insert(node.id(), node.clone());
    for child in node.children() {
        populate_node_map(node_map, &child);
    }
}
