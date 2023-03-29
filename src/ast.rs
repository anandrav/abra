use crate::operators::BinOpcode;
// use pest::error::{Error, ErrorVariant, InputLocation::Pos};
use crate::types::{self, Prov};
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
pub type PatAnnotated = (Rc<Pat>, Option<Rc<AstType>>);

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
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.stmtkind {
            StmtKind::Let((pat, ty), expr) => {
                let mut children: Vec<Rc<dyn Node>> = vec![pat.clone() as Rc<dyn Node>];
                if let Some(ty) = ty {
                    children.push(ty.clone());
                }
                children.push(expr.clone());
                children
            }
            StmtKind::Expr(expr) => vec![expr.clone()],
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum StmtKind {
    Let(PatAnnotated, Rc<Expr>),
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
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.exprkind {
            ExprKind::Var(_) => vec![],
            ExprKind::Unit => vec![],
            ExprKind::Int(_) => vec![],
            ExprKind::Bool(_) => vec![],
            ExprKind::Str(_) => vec![],
            // TODO: output of function needs to be annotated as well!
            ExprKind::Func(args, ty_opt, body) => {
                let mut children: Vec<Rc<dyn Node>> = Vec::new();
                args.iter().for_each(|(pat, ty_opt)| {
                    children.push(pat.clone());
                    if let Some(ty) = ty_opt {
                        children.push(ty.clone())
                    }
                });
                if let Some(ty) = ty_opt {
                    children.push(ty.clone())
                }
                children.push(body.clone());
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
            ExprKind::FuncAp(func, args) => {
                let mut children: Vec<Rc<dyn Node>> = vec![func.clone() as Rc<dyn Node>];
                children.extend(args.iter().map(|a| a.clone() as Rc<dyn Node>));
                children
            }
            ExprKind::Tuple(exprs) => exprs
                .iter()
                .map(|e| e.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
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
    Func(Vec<PatAnnotated>, Option<Rc<AstType>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    // Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>, Option<Rc<Expr>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>),
    Tuple(Vec<Rc<Expr>>),
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
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.patkind {
            PatKind::Var(_) => vec![],
            PatKind::Tuple(pats) => pats
                .iter()
                .map(|p| p.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
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
    Tuple(Vec<Rc<Pat>>),
}

impl PatKind {
    pub fn get_identifier(&self) -> Identifier {
        match self {
            PatKind::Var(id) => id.clone(),
            PatKind::Tuple(_) => panic!("Pattern is not a variable"),
        }
    }
}

#[derive(Debug, PartialEq)]
pub struct AstType {
    pub typekind: Rc<TypeKind>,
    pub span: Span,
    pub id: Id,
}

pub fn ast_type_to_statics_type(ast_type: Rc<AstType>) -> Rc<types::SType> {
    match &*ast_type.typekind {
        TypeKind::Unit => types::SType::make_unit(Prov::Node(ast_type.id())),
        TypeKind::Int => types::SType::make_int(Prov::Node(ast_type.id())),
        TypeKind::Bool => types::SType::make_bool(Prov::Node(ast_type.id())),
        TypeKind::Str => types::SType::make_string(Prov::Node(ast_type.id())),
        TypeKind::Arrow(lhs, rhs) => Rc::new(types::SType {
            typekind: types::STypeKind::Arrow(
                vec![ast_type_to_statics_type(lhs.clone())],
                ast_type_to_statics_type(rhs.clone()),
            ),
            prov: Prov::Node(ast_type.id()),
        }),
        TypeKind::Tuple(types) => {
            let mut statics_types = Vec::new();
            for t in types {
                statics_types.push(ast_type_to_statics_type(t.clone()));
            }
            Rc::new(types::SType {
                typekind: types::STypeKind::Tuple(statics_types),
                prov: Prov::Node(ast_type.id()),
            })
        }
    }
}

impl Node for AstType {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.typekind {
            TypeKind::Unit | TypeKind::Int | TypeKind::Bool | TypeKind::Str => vec![],
            TypeKind::Arrow(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            TypeKind::Tuple(types) => types
                .iter()
                .map(|t| t.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
        }
    }
}

#[derive(Debug, PartialEq)]
pub enum TypeKind {
    Unit,
    Int,
    Bool,
    Str,
    // TODO: make this nary as well
    Arrow(Rc<AstType>, Rc<AstType>),
    Tuple(Vec<Rc<AstType>>),
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl Span {
    pub fn lines_and_columns(&self, source: &str) -> ((usize, usize), (usize, usize)) {
        let lo_line = source[..=self.lo].lines().count() - 1;
        let num_chars_of_lines_before = source
            .lines()
            .enumerate()
            .filter(|(i, _)| *i < lo_line)
            .map(|(_, l)| l.len())
            .sum::<usize>()
            + lo_line; // account for newlines
        let lo_col = self.lo - num_chars_of_lines_before;

        let hi_line = source[..=self.hi].lines().count() - 1;
        let num_chars_of_lines_before = source
            .lines()
            .enumerate()
            .filter(|(i, _)| *i < hi_line)
            .map(|(_, l)| l.len())
            .sum::<usize>()
            + hi_line; // account for newlines
        let hi_col = self.hi - num_chars_of_lines_before;
        ((lo_line, lo_col), (hi_line, hi_col))
    }

    pub fn display(&self, source: &str, detail: &str) -> String {
        let mut s = String::new();
        let ((lo_line, lo_col), (hi_line, hi_col)) = self.lines_and_columns(source);
        if lo_line != hi_line {
            s.push_str(&format!(
                "--> On lines {}-{}, {}\n",
                lo_line, hi_line, detail
            ));
        } else {
            s.push_str(&format!("--> On line {}, {}\n", lo_line, detail));
        }
        for line_number in lo_line..=hi_line {
            let line = source.lines().nth(line_number).unwrap();
            s.push_str(&format!("{:3} | {}\n", line_number, line));

            let pad_before = if line_number == lo_line { lo_col } else { 0 };
            let num_tabs = line.chars().take(pad_before).filter(|c| *c == '\t').count();
            let pad_before_in_spaces = pad_before + num_tabs * 3;

            let pad_end = if line_number == hi_line {
                line.len() - hi_col
            } else {
                0
            };

            let underline = line.len() - pad_end - pad_before;
            s.push_str(&format!("{:3} | ", "")); // line number placeholder
            s.push_str(&format!("{:1$}", "", pad_before_in_spaces)); // pad before
            s.push_str(&format!("{:^<1$}\n", "", underline)); // underline
        }
        s
    }
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

pub fn parse_pat_annotated(pair: Pair<Rule>, _pratt: &PrattParser<Rule>) -> PatAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::pattern_annotated => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_pat(pat_pair, _pratt);
            let ty = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), _pratt));
            (pat, ty)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_func_out_annotation(pair: Pair<Rule>, _pratt: &PrattParser<Rule>) -> Rc<AstType> {
    let rule = pair.as_rule();
    match rule {
        Rule::func_out_annotation => {
            let inner: Vec<_> = pair.into_inner().collect();
            let type_pair = inner[0].clone();
            parse_type_term(type_pair, _pratt)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
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
        Rule::tuple_pat => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_pat(pair.clone(), _pratt))
                .collect();
            Rc::new(Pat {
                patkind: Rc::new(PatKind::Tuple(pats)),
                span,
                id: Id::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_type_pratt(pairs: Pairs<Rule>) -> Rc<AstType> {
    let pratt = PrattParser::new().op(Op::infix(Rule::type_op_arrow, Assoc::Right));
    pratt
        .map_primary(|primary| parse_type_term(primary, &pratt))
        .map_infix(|lhs, op, rhs| {
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Arrow(lhs, rhs)),
                span: Span::from(op.as_span()),
                id: Id::new(),
            })
        })
        .parse(pairs)
}

pub fn parse_type_term(pair: Pair<Rule>, _pratt: &PrattParser<Rule>) -> Rc<AstType> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::typ => parse_type_pratt(pair.into_inner()),
        Rule::type_literal_unit => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Unit),
            span,
            id: Id::new(),
        }),
        Rule::type_literal_number => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Int),
            span,
            id: Id::new(),
        }),
        Rule::type_literal_bool => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Bool),
            span,
            id: Id::new(),
        }),
        Rule::type_literal_string => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Str),
            span,
            id: Id::new(),
        }),
        Rule::tuple_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let types = inner
                .into_iter()
                .map(|pair| parse_type_term(pair, _pratt))
                .collect();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Tuple(types)),
                span,
                id: Id::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_stmt(pair: Pair<Rule>, pratt: &PrattParser<Rule>) -> Rc<Stmt> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::let_statement => {
            let pat_annotated = parse_pat_annotated(inner[0].clone(), pratt);
            let expr = parse_expr_pratt(Pairs::single(inner[1].clone()), pratt);
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::Let(pat_annotated, expr)),
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
            let mut n = 0;
            let mut args = vec![];
            while let Rule::pattern_annotated = inner[n].as_rule() {
                let pat_annotated = parse_pat_annotated(inner[n].clone(), pratt);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ty_out = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), pratt))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), pratt);
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Func(args, ty_out, body)),
                span,
                id: Id::new(),
            })
        }
        Rule::func_call_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let f = parse_expr_pratt(Pairs::single(inner[0].clone()), pratt);
            let arg1 = parse_expr_pratt(Pairs::single(inner[1].clone()), pratt);
            let mut args = vec![arg1];
            for p in &inner[2..] {
                args.push(parse_expr_pratt(Pairs::single(p.clone()), pratt));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::FuncAp(f, args)),
                span,
                id: Id::new(),
            })
        }
        Rule::tuple_expr => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), pratt));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Tuple(exprs)),
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

// TODO: this never errors lol
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

pub fn initialize_node_map(node_map: &mut NodeMap, node: &Rc<dyn Node>) {
    node_map.insert(node.id(), node.clone());
    for child in node.children() {
        initialize_node_map(node_map, &child);
    }
}
