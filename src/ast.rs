use crate::operators::BinOpcode;
// use pest::error::{Error, ErrorVariant, InputLocation::Pos};
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

pub type ArgAnnotated = (Rc<Pat>, Option<Rc<AstType>>);

#[derive(Debug, Clone, PartialEq)]
pub struct InterfaceAnnotation {
    pub ident: Identifier,
    pub span: Span,
    pub id: Id,
}
impl Node for InterfaceAnnotation {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id
    }
    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![]
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct MethodName {
    pub ident: Identifier,
    pub span: Span,
    pub id: Id,
}
impl Node for MethodName {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id
    }
    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![]
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

pub type PatAnnotated = (Rc<Pat>, Option<Rc<AstType>>);

#[derive(Debug, Clone)]
pub struct Toplevel {
    pub statements: Vec<Rc<Stmt>>,
    pub span: Span,
    pub id: Id,
}

impl Node for Toplevel {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        self.statements
            .iter()
            .map(|i| i.clone() as Rc<dyn Node>)
            .collect()
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDef {
    pub kind: TypeDefKind,
    pub span: Span,
    pub id: Id,
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeDefKind {
    Alias(Identifier, Rc<AstType>),
    Adt(Identifier, Vec<Rc<AstType>>, Vec<Rc<Variant>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct Variant {
    pub ctor: Identifier,
    pub data: Option<Rc<AstType>>,

    pub span: Span,
    pub id: Id,
}

impl Node for Variant {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &self.data {
            Some(ty) => vec![ty.clone()],
            None => vec![],
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

impl Node for TypeDef {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> Id {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &self.kind {
            TypeDefKind::Alias(_, ty) => vec![ty.clone()],
            TypeDefKind::Adt(..) => todo!(),
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

impl std::fmt::Debug for dyn Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("span", &self.span())
            .field("id", &self.id())
            .finish()
    }
}

pub trait Node {
    fn span(&self) -> Span;
    fn id(&self) -> Id;
    fn children(&self) -> Vec<Rc<dyn Node>>;

    fn to_stmt(&self) -> Option<Stmt>;
}

#[derive(Debug, Clone, PartialEq)]
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
            StmtKind::LetFunc(id, args, ty, expr) => {
                let mut children: Vec<Rc<dyn Node>> = vec![id.clone() as Rc<dyn Node>];
                for (pat, annot) in args {
                    children.push(pat.clone() as Rc<dyn Node>);
                    match annot {
                        Some(ty) => children.push(ty.clone()),
                        None => {}
                    }
                }
                if let Some(ty) = ty {
                    children.push(ty.clone());
                }
                children.push(expr.clone());
                children
            }
            StmtKind::Let((pat, ty), expr) => {
                let mut children: Vec<Rc<dyn Node>> = vec![pat.clone() as Rc<dyn Node>];
                if let Some(ty) = ty {
                    children.push(ty.clone());
                }
                children.push(expr.clone());
                children
            }
            StmtKind::Expr(expr) => vec![expr.clone()],
            StmtKind::TypeDef(tydefkind) => match &**tydefkind {
                TypeDefKind::Alias(_, ty) => vec![ty.clone()],
                TypeDefKind::Adt(_, params, variants) => {
                    let mut children: Vec<Rc<dyn Node>> = Vec::new();
                    for param in params {
                        children.push(param.clone());
                    }
                    for variant in variants {
                        children.push(variant.clone() as Rc<dyn Node>);
                    }
                    children
                }
            },
            StmtKind::InterfaceDef(_, props) => {
                let mut children: Vec<Rc<dyn Node>> = Vec::new();
                for prop in props {
                    children.push(prop.clone() as Rc<dyn Node>);
                }
                children
            }
            StmtKind::InterfaceImpl(_, ty, stmts) => {
                let mut children: Vec<Rc<dyn Node>> = vec![ty.clone()];
                for stmt in stmts {
                    children.push(stmt.clone() as Rc<dyn Node>);
                }
                children
            }
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        Some(self.clone())
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum StmtKind {
    LetFunc(Rc<Pat>, Vec<ArgAnnotated>, Option<Rc<AstType>>, Rc<Expr>),
    Let(PatAnnotated, Rc<Expr>),
    Expr(Rc<Expr>),
    TypeDef(Rc<TypeDefKind>),
    InterfaceDef(Identifier, Vec<Rc<InterfaceProperty>>),
    InterfaceImpl(Identifier, Rc<AstType>, Vec<Rc<Stmt>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct InterfaceProperty {
    pub ident: Identifier,
    pub ty: Rc<AstType>,
}

impl Node for InterfaceProperty {
    fn span(&self) -> Span {
        self.ty.span()
    }
    fn id(&self) -> Id {
        self.ty.id()
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![self.ty.clone()]
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
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
            ExprKind::List(exprs) => exprs.iter().map(|e| e.clone() as Rc<dyn Node>).collect(),
            // TODO: output of function needs to be annotated as well!
            ExprKind::Func(args, ty_opt, body) => {
                let mut children: Vec<Rc<dyn Node>> = Vec::new();
                args.iter().for_each(|(pat, annot)| {
                    children.push(pat.clone());
                    match annot {
                        Some(ty) => children.push(ty.clone()),
                        None => {}
                    }
                });
                if let Some(ty) = ty_opt {
                    children.push(ty.clone())
                }
                children.push(body.clone());
                children
            }
            ExprKind::If(cond, then, els) => {
                let mut children: Vec<Rc<dyn Node>> = vec![cond.clone()];
                children.push(then.clone());
                if let Some(els) = els {
                    children.push(els.clone());
                }
                children
            }
            ExprKind::Block(stmts) => stmts
                .iter()
                .map(|s| s.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
            ExprKind::BinOp(lhs, _, rhs) => vec![lhs.clone(), rhs.clone()],
            ExprKind::FuncAp(func, args) => {
                let mut children: Vec<Rc<dyn Node>> = vec![func.clone() as Rc<dyn Node>];
                children.extend(args.iter().map(|a| a.clone() as Rc<dyn Node>));
                children
            }
            ExprKind::MethodAp(obj, _, args) => {
                let mut children: Vec<Rc<dyn Node>> = vec![obj.clone() as Rc<dyn Node>];
                children.extend(args.iter().map(|a| a.clone() as Rc<dyn Node>));
                children
            }
            ExprKind::Tuple(exprs) => exprs
                .iter()
                .map(|e| e.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
            ExprKind::Match(expr, arms) => {
                let mut children: Vec<Rc<dyn Node>> = vec![expr.clone()];
                for arm in arms {
                    children.push(arm.pat.clone() as Rc<dyn Node>);
                    children.push(arm.expr.clone() as Rc<dyn Node>);
                }
                children
            }
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum ExprKind {
    // EmptyHole,
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    List(Vec<Rc<Expr>>),
    Func(Vec<ArgAnnotated>, Option<Rc<AstType>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Option<Rc<Expr>>),
    Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>),
    MethodAp(Rc<Expr>, MethodName, Vec<Rc<Expr>>),
    Tuple(Vec<Rc<Expr>>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct MatchArm {
    pub pat: Rc<Pat>,
    pub expr: Rc<Expr>,
}

// pub type MatchArm = (Rc<Pat>, Rc<Expr>);

#[derive(Debug, Clone, PartialEq)]
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
            PatKind::Wildcard => vec![],
            PatKind::Var(_) => vec![],
            PatKind::Unit => vec![],
            PatKind::Int(_) => vec![],
            PatKind::Bool(_) => vec![],
            PatKind::Str(_) => vec![],
            PatKind::Variant(_, pat_opt) => {
                if let Some(pat) = pat_opt {
                    vec![pat.clone()]
                } else {
                    vec![]
                }
            }
            PatKind::Tuple(pats) => pats
                .iter()
                .map(|p| p.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PatKind {
    // EmptyHole,
    Wildcard,
    Var(Identifier),
    Variant(Identifier, Option<Rc<Pat>>),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Tuple(Vec<Rc<Pat>>),
}

impl PatKind {
    pub fn get_identifier_of_variable(&self) -> Identifier {
        match self {
            PatKind::Var(id) => id.clone(),
            _ => {
                panic!("Pattern is not a variable")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq)]
pub struct AstType {
    pub typekind: Rc<TypeKind>,
    pub span: Span,
    pub id: Id,
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
            TypeKind::Poly(_, _)
            | TypeKind::Alias(_)
            | TypeKind::Unit
            | TypeKind::Int
            | TypeKind::Bool
            | TypeKind::Str => {
                vec![]
            }
            TypeKind::Ap(_ty, params) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                children.extend(params.iter().map(|t| t.clone() as Rc<dyn Node>));
                children
            }
            TypeKind::Function(lhs, rhs) => {
                let mut children: Vec<Rc<dyn Node>> = vec![];
                children.extend(lhs.iter().map(|t| t.clone() as Rc<dyn Node>));
                children.push(rhs.clone() as Rc<dyn Node>);
                children
            }
            TypeKind::Tuple(types) => types
                .iter()
                .map(|t| t.clone() as Rc<dyn Node>)
                .collect::<Vec<_>>(),
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum TypeKind {
    Poly(Identifier, Vec<Identifier>),
    Alias(Identifier),
    Ap(Identifier, Vec<Rc<AstType>>),
    Unit,
    Int,
    Bool,
    Str,
    // TODO: make Arrow nary as well
    Function(Vec<Rc<AstType>>, Rc<AstType>),
    Tuple(Vec<Rc<AstType>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl std::fmt::Display for Id {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id[{}]", self.id)
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

        let hi_line = source[..self.hi].lines().count() - 1;
        let num_chars_of_lines_before = source
            .lines()
            .enumerate()
            .filter(|(i, _)| *i < hi_line)
            .map(|(_, l)| l.len())
            .sum::<usize>()
            + hi_line; // account for newlines
        let hi_col = self.hi - num_chars_of_lines_before - 1;
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
    MyParser::parse(Rule::toplevel, source).map_err(|e| e.to_string())
}

pub fn parse_func_arg_annotation(pair: Pair<Rule>) -> ArgAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::func_arg => {
            println!("func_arg detected");
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair);
            let annot = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone()));
            (pat, annot)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_annotated_let_pattern(pair: Pair<Rule>) -> PatAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::let_pattern_annotated => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair);
            let ty = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone()));
            (pat, ty)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_func_out_annotation(pair: Pair<Rule>) -> Rc<AstType> {
    let rule = pair.as_rule();
    match rule {
        Rule::func_out_annotation => {
            let inner: Vec<_> = pair.into_inner().collect();
            let type_pair = inner[0].clone();
            parse_type_term(type_pair)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_let_pattern(pair: Pair<Rule>) -> Rc<Pat> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_let_pattern(pair)
        }
        Rule::identifier => Rc::new(Pat {
            patkind: Rc::new(PatKind::Var(pair.as_str().to_owned())),
            span,
            id: Id::new(),
        }),
        Rule::let_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_let_pattern(pair.clone()))
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

pub fn parse_match_pattern(pair: Pair<Rule>) -> Rc<Pat> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::match_pattern => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_match_pattern(pair)
        }
        Rule::match_pattern_variable => Rc::new(Pat {
            patkind: Rc::new(PatKind::Var(pair.as_str()[1..].to_owned())),
            span,
            id: Id::new(),
        }),
        Rule::match_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_match_pattern(pair.clone()))
                .collect();
            Rc::new(Pat {
                patkind: Rc::new(PatKind::Tuple(pats)),
                span,
                id: Id::new(),
            })
        }
        Rule::match_pattern_variant => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let pat = inner.get(1).map(|pair| parse_match_pattern(pair.clone()));
            Rc::new(Pat {
                patkind: Rc::new(PatKind::Variant(name, pat)),
                span,
                id: Id::new(),
            })
        }
        Rule::wildcard => Rc::new(Pat {
            patkind: Rc::new(PatKind::Wildcard),
            span,
            id: Id::new(),
        }),
        Rule::literal_unit => Rc::new(Pat {
            patkind: Rc::new(PatKind::Unit),
            span,
            id: Id::new(),
        }),
        Rule::literal_number => Rc::new(Pat {
            patkind: Rc::new(PatKind::Int(pair.as_str().parse().unwrap())),
            span,
            id: Id::new(),
        }),
        Rule::literal_bool => Rc::new(Pat {
            patkind: Rc::new(PatKind::Bool(pair.as_str().parse().unwrap())),
            span,
            id: Id::new(),
        }),
        Rule::literal_string => Rc::new(Pat {
            patkind: Rc::new(PatKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
            id: Id::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_type_term(pair: Pair<Rule>) -> Rc<AstType> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::type_poly => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str()[1..].to_owned();
            let mut interfaces = vec![];
            for (i, pair) in inner.iter().enumerate() {
                if i == 0 {
                    continue;
                }
                let interface = pair.as_str().to_owned();
                interfaces.push(interface);
            }
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Poly(name, interfaces)),
                span,
                id: Id::new(),
            })
        }
        Rule::identifier => {
            let ident = pair.as_str().to_string();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Alias(ident)),
                span,
                id: Id::new(),
            })
        }
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
            let types = inner.into_iter().map(parse_type_term).collect();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Tuple(types)),
                span,
                id: Id::new(),
            })
        }
        Rule::type_ap => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let types = inner.into_iter().skip(1).map(parse_type_term).collect();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Ap(name, types)),
                span,
                id: Id::new(),
            })
        }
        Rule::func_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let len = inner.len();
            let args: Vec<_> = inner
                .clone()
                .into_iter()
                .take(len - 1)
                .map(parse_type_term)
                .collect();
            let ret = parse_type_term(inner.last().unwrap().clone());
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Function(args, ret)),
                span,
                id: Id::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", pair),
    }
}

pub fn parse_stmt(pair: Pair<Rule>) -> Rc<Stmt> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::let_func_statement => {
            let mut n = 0;
            let mut args = vec![];
            let ident = parse_let_pattern(inner[0].clone());
            n += 1;
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone());
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ty_out = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone()))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()));
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::LetFunc(ident, args, ty_out, body)),
                span,
                id: Id::new(),
            })
        }
        Rule::let_statement => {
            let pat_annotated = parse_annotated_let_pattern(inner[0].clone());
            let expr = parse_expr_pratt(Pairs::single(inner[1].clone()));
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::Let(pat_annotated, expr)),
                span,
                id: Id::new(),
            })
        }
        Rule::expression_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()));
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::Expr(expr)),
                span,
                id: Id::new(),
            })
        }
        Rule::typealias => {
            let ident = inner[0].as_str().to_string();
            let definition = parse_type_term(inner[1].clone());
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::TypeDef(Rc::new(TypeDefKind::Alias(
                    ident, definition,
                )))),
                span,
                id: Id::new(),
            })
        }
        Rule::adt_declaration => {
            let ident = inner[0].as_str().to_string();
            let mut n = 1;
            let mut params = vec![];
            while let Rule::type_poly = inner[n].as_rule() {
                params.push(parse_type_term(inner[n].clone()));
                n += 1;
            }
            let mut variants = vec![];
            while let Some(pair) = inner.get(n) {
                let variant = parse_variant(pair.clone());
                variants.push(variant);
                n += 1;
            }
            Rc::new(Stmt {
                stmtkind: Rc::new(StmtKind::TypeDef(Rc::new(TypeDefKind::Adt(
                    ident, params, variants,
                )))),
                span,
                id: Id::new(),
            })
        }
        Rule::interface_declaration => {
            let ident = inner[0].as_str().to_string();
            let mut n = 1;
            let mut methods = vec![];
            while let Some(pair) = inner.get(n) {
                let method = parse_interface_method(pair.clone());
                methods.push(Rc::new(method));
                n += 1;
            }
            Rc::new(Stmt {
                stmtkind: StmtKind::InterfaceDef(ident, methods).into(),
                span,
                id: Id::new(),
            })
        }
        Rule::interface_implementation => {
            let ident = inner[0].as_str().to_string();
            let ty = parse_type_term(inner[1].clone());
            let mut n = 2;
            let mut stmts = vec![];
            while let Some(pair) = inner.get(n) {
                let stmt = parse_stmt(pair.clone());
                stmts.push(stmt);
                n += 1;
            }
            Rc::new(Stmt {
                stmtkind: StmtKind::InterfaceImpl(ident, ty, stmts).into(),
                span,
                id: Id::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_interface_method(pair: Pair<Rule>) -> InterfaceProperty {
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::interface_property => {
            let ident = inner[0].as_str().to_string();
            let ty = parse_type_term(inner[1].clone());
            InterfaceProperty { ident, ty }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_variant(pair: Pair<Rule>) -> Rc<Variant> {
    let span = Span::from(pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::variant => {
            let ident = inner[0].as_str().to_string();
            let n = 1;
            // while let Rule::type_poly = inner[n].as_rule() {
            //     type_params.push(inner[n].as_str().to_string());
            //     n += 1;
            // }
            let data = if let Some(pair) = inner.get(n) {
                let data = parse_type_term(pair.clone());
                Some(data)
            } else {
                None
            };
            Rc::new(Variant {
                ctor: ident,
                data,
                span,
                id: Id::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_expr_term(pair: Pair<Rule>) -> Rc<Expr> {
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
        Rule::expression => parse_expr_pratt(pair.into_inner()),
        // All rules listed below should be non-operator expressions
        Rule::block_expression => {
            let inner = pair.into_inner();
            let mut statements: Vec<Rc<Stmt>> = Vec::new();
            for pair in inner {
                statements.push(parse_stmt(pair));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Block(statements)),
                span,
                id: Id::new(),
            })
        }
        Rule::if_else_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()));
            let e1 = parse_expr_pratt(Pairs::single(inner[1].clone()));
            let e2 = if inner.len() == 3 {
                Some(parse_expr_pratt(Pairs::single(inner[2].clone())))
            } else {
                None
            };
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::If(cond, e1, e2)),
                span,
                id: Id::new(),
            })
        }
        Rule::match_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()));
            let mut arms = vec![];
            fn parse_match_arm(pair: &Pair<Rule>) -> MatchArm {
                let inner: Vec<_> = pair.clone().into_inner().collect();
                let pat = parse_match_pattern(inner[0].clone());
                let expr = parse_expr_pratt(Pairs::single(inner[1].clone()));
                MatchArm { pat, expr }
            }
            for pair in &inner[1..] {
                arms.push(parse_match_arm(pair));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Match(expr, arms)),
                span,
                id: Id::new(),
            })
        }
        Rule::func_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut n = 0;
            let mut args = vec![];
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone());
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ty_out = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone()))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()));
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::Func(args, ty_out, body)),
                span,
                id: Id::new(),
            })
        }
        Rule::func_call_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let f = parse_expr_pratt(Pairs::single(inner[0].clone()));
            let inner: Vec<_> = inner[1].clone().into_inner().collect();
            let mut args = vec![];
            for p in &inner[0..] {
                args.push(parse_expr_pratt(Pairs::single(p.clone())));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::FuncAp(f, args)),
                span,
                id: Id::new(),
            })
        }
        Rule::method_call_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let receiver = parse_expr_pratt(Pairs::single(inner[0].clone()));
            let Rule::method_call_ident_and_args = inner[1].as_rule() else { unreachable!() };
            let inner: Vec<_> = inner[1].clone().into_inner().collect();
            let method = MethodName {
                ident: inner[0].as_str().to_string(),
                span: inner[0].as_span().into(),
                id: Id::new(),
            };
            let inner: Vec<_> = inner[1].clone().into_inner().collect();
            let mut args = vec![];
            for p in &inner[0..] {
                args.push(parse_expr_pratt(Pairs::single(p.clone())));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::MethodAp(receiver, method, args)),
                span,
                id: Id::new(),
            })
        }
        Rule::tuple_expr => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p)));
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
        Rule::literal_list => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p)));
            }
            Rc::new(Expr {
                exprkind: Rc::new(ExprKind::List(exprs)),
                span,
                id: Id::new(),
            })
        }
        Rule::identifier => Rc::new(Expr {
            exprkind: Rc::new(ExprKind::Var(pair.as_str().to_owned())),
            span,
            id: Id::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub fn parse_toplevel(pairs: Pairs<Rule>) -> Rc<Toplevel> {
    let mut items = Vec::new();
    let pairs: Vec<_> = pairs.into_iter().collect();
    for pair in &pairs {
        if pair.as_rule() == Rule::EOI {
            break;
        }
        let stmt = parse_stmt(pair.clone());
        items.push(stmt)
    }
    let span1: Span = pairs.first().unwrap().as_span().into();
    let span2: Span = pairs.last().unwrap().as_span().into();
    Rc::new(Toplevel {
        statements: items,
        span: Span {
            lo: span1.lo,
            hi: span2.hi,
        }, // TODO
        id: Id::new(),
    })
}

pub fn parse_expr_pratt(pairs: Pairs<Rule>) -> Rc<Expr> {
    let pratt = PrattParser::new()
        .op(Op::infix(Rule::op_eq, Assoc::Left))
        .op(Op::infix(Rule::op_concat, Assoc::Right))
        .op(Op::infix(Rule::op_and, Assoc::Left) | Op::infix(Rule::op_or, Assoc::Left))
        .op(Op::infix(Rule::op_lt, Assoc::Left)
            | Op::infix(Rule::op_gt, Assoc::Left)
            | Op::infix(Rule::op_lte, Assoc::Left)
            | Op::infix(Rule::op_gte, Assoc::Left))
        .op(Op::infix(Rule::op_addition, Assoc::Left)
            | Op::infix(Rule::op_subtraction, Assoc::Left))
        .op(Op::infix(Rule::op_multiplication, Assoc::Left)
            | Op::infix(Rule::op_division, Assoc::Left)
            | Op::infix(Rule::op_mod, Assoc::Left));
    pratt
        .map_primary(parse_expr_term)
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
                Rule::op_gte => BinOpcode::GreaterThanOrEqual,
                Rule::op_lte => BinOpcode::LessThanOrEqual,
                Rule::op_addition => BinOpcode::Add,
                Rule::op_subtraction => BinOpcode::Subtract,
                Rule::op_multiplication => BinOpcode::Multiply,
                Rule::op_division => BinOpcode::Divide,
                Rule::op_mod => BinOpcode::Mod,
                Rule::op_and => BinOpcode::And,
                Rule::op_or => BinOpcode::Or,
                Rule::op_concat => BinOpcode::Concat,
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
pub fn parse_or_err(source: &str) -> Result<Rc<Toplevel>, String> {
    let pairs = get_pairs(source)?;
    // at this point, we know it's syntactically correct,
    // so we figure out operator precedence using the pratt parser

    Ok(parse_toplevel(pairs))
}

pub type NodeMap = HashMap<Id, Rc<dyn Node>>;

pub fn initialize_node_map(node_map: &mut NodeMap, node: &Rc<dyn Node>) {
    node_map.insert(node.id(), node.clone());
    for child in node.children() {
        initialize_node_map(node_map, &child);
    }
}
