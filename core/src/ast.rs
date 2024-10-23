use crate::SourceFile;
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

pub(crate) type Identifier = String;

pub(crate) type ArgAnnotated = (Rc<Pat>, Option<Rc<AstType>>);

#[derive(Debug, Clone)]
pub(crate) struct Sources {
    pub(crate) filename_to_source: HashMap<String, String>,
}

pub(crate) type PatAnnotated = (Rc<Pat>, Option<Rc<AstType>>);

#[derive(Debug, Clone)]
pub(crate) struct FileAst {
    pub(crate) statements: Vec<Rc<Stmt>>,
    pub(crate) name: String,

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for FileAst {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        self.statements
            .iter()
            .map(|i| i.clone() as Rc<dyn Node>)
            .collect()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypeDefKind {
    // Alias(Identifier, Rc<AstType>),
    Enum(Rc<EnumDef>),
    Struct(Rc<StructDef>),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct EnumDef {
    pub(crate) name: Identifier,
    pub(crate) ty_args: Vec<Rc<AstType>>,
    pub(crate) variants: Vec<Rc<Variant>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct StructDef {
    pub(crate) name: Identifier,
    pub(crate) ty_args: Vec<Rc<AstType>>,
    pub(crate) fields: Vec<Rc<StructField>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Variant {
    pub(crate) ctor: Identifier,
    pub(crate) data: Option<Rc<AstType>>,

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Variant {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &self.data {
            Some(ty) => vec![ty.clone()],
            None => vec![],
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct StructField {
    pub(crate) ident: Identifier,
    pub(crate) ty: Rc<AstType>,

    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for StructField {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![self.ty.clone()]
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

// TODO: convert this to an Enum
pub(crate) trait Node {
    fn span(&self) -> Span;
    fn id(&self) -> NodeId;
    fn children(&self) -> Vec<Rc<dyn Node>>;

    fn to_expr(&self) -> Option<Expr> {
        None
    }
    fn to_stmt(&self) -> Option<Stmt> {
        None
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Stmt {
    pub(crate) kind: Rc<StmtKind>,
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Stmt {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            StmtKind::FuncDef(f) => {
                let mut children: Vec<Rc<dyn Node>> = vec![f.name.clone() as Rc<dyn Node>];
                for (pat, annot) in f.args.iter() {
                    children.push(pat.clone() as Rc<dyn Node>);
                    match annot {
                        Some(ty) => children.push(ty.clone()),
                        None => {}
                    }
                }
                if let Some(ty) = &f.ret_type {
                    children.push(ty.clone());
                }
                children.push(f.body.clone());
                children
            }
            StmtKind::Let(_mutable, (pat, ty), expr) => {
                let mut children: Vec<Rc<dyn Node>> = vec![pat.clone() as Rc<dyn Node>];
                if let Some(ty) = ty {
                    children.push(ty.clone());
                }
                children.push(expr.clone());
                children
            }
            StmtKind::Set(lhs, rhs) => vec![lhs.clone(), rhs.clone()],
            StmtKind::Expr(expr) => vec![expr.clone()],
            StmtKind::TypeDef(tydefkind) => match &**tydefkind {
                // TypeDefKind::Alias(_, ty) => vec![ty.clone()],
                // TODO this is redundant, use the Node::children() implementation
                TypeDefKind::Enum(e) => {
                    let mut children: Vec<Rc<dyn Node>> = Vec::new();
                    for param in e.ty_args.iter() {
                        children.push(param.clone());
                    }
                    for variant in e.variants.iter() {
                        children.push(variant.clone() as Rc<dyn Node>);
                    }
                    children
                }
                TypeDefKind::Struct(s) => {
                    let mut children: Vec<Rc<dyn Node>> = Vec::new();
                    for ty in s.ty_args.iter() {
                        children.push(ty.clone());
                    }
                    for field in s.fields.iter() {
                        children.push(field.clone() as Rc<dyn Node>);
                    }
                    children
                }
            },
            StmtKind::InterfaceDef(i) => {
                let mut children: Vec<Rc<dyn Node>> = Vec::new();
                for prop in i.props.iter() {
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
            StmtKind::Import(_) => vec![],
        }
    }

    fn to_stmt(&self) -> Option<Stmt> {
        Some(self.clone())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum StmtKind {
    Let(bool, PatAnnotated, Rc<Expr>), // bool is whether it's mutable
    Set(Rc<Expr>, Rc<Expr>),
    Expr(Rc<Expr>),
    // TODO: change these to be "FileAstItem". FileAstItem = FuncDef | TypeDef | InterfaceDef | InterfaceImpl | Stmt
    // TODO: don't use FuncDef for interface methods
    FuncDef(Rc<FuncDef>),
    TypeDef(Rc<TypeDefKind>),
    InterfaceDef(Rc<InterfaceDef>),
    InterfaceImpl(Identifier, Rc<AstType>, Vec<Rc<Stmt>>),
    Import(Identifier),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct FuncDef {
    pub(crate) name: Rc<Pat>, // TODO: Don't use Rc<Pat> for the name, just use Identifier. If need be, make struct for Identifier with span and id
    pub(crate) args: Vec<ArgAnnotated>,
    pub(crate) ret_type: Option<Rc<AstType>>,
    pub(crate) body: Rc<Expr>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceDef {
    pub(crate) name: Identifier,
    pub(crate) props: Vec<Rc<InterfaceProperty>>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct InterfaceProperty {
    pub(crate) ident: Identifier,
    pub(crate) ty: Rc<AstType>,
}

impl Node for InterfaceProperty {
    fn span(&self) -> Span {
        self.ty.span()
    }
    fn id(&self) -> NodeId {
        self.ty.id()
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        vec![self.ty.clone()]
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Expr {
    pub(crate) kind: Rc<ExprKind>,
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Expr {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            ExprKind::Identifier(_) => vec![],
            ExprKind::Unit => vec![],
            ExprKind::Int(_) => vec![],
            ExprKind::Float(_) => vec![],
            ExprKind::Bool(_) => vec![],
            ExprKind::Str(_) => vec![],
            ExprKind::List(exprs) => exprs.iter().map(|e| e.clone() as Rc<dyn Node>).collect(),
            ExprKind::Array(exprs) => exprs.iter().map(|e| e.clone() as Rc<dyn Node>).collect(),
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
            ExprKind::WhileLoop(cond, body) => vec![cond.clone(), body.clone()],
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
            ExprKind::MemberAccess(expr, field) => vec![expr.clone(), field.clone()], // TODO: should field really be an expression? maybe just an identifier?
            ExprKind::IndexAccess(expr, index) => vec![expr.clone(), index.clone()],
        }
    }

    fn to_expr(&self) -> Option<Expr> {
        Some(self.clone())
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ExprKind {
    // EmptyHole,
    Identifier(Identifier),
    Unit,
    Int(i64),
    Float(String), // represented as String to allow Eq and Hash
    Bool(bool),
    Str(String),
    List(Vec<Rc<Expr>>),
    Array(Vec<Rc<Expr>>),
    Func(Vec<ArgAnnotated>, Option<Rc<AstType>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Option<Rc<Expr>>),
    WhileLoop(Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<MatchArm>),
    Block(Vec<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Vec<Rc<Expr>>),
    Tuple(Vec<Rc<Expr>>),
    MemberAccess(Rc<Expr>, Rc<Expr>),
    IndexAccess(Rc<Expr>, Rc<Expr>),
}

#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BinOpcode {
    // comparison
    Equal,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    // numeric
    Add,
    Subtract,
    Multiply,
    Divide,
    Mod,
    Pow,
    // boolean
    And,
    Or,
    // string
    Concat,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct MatchArm {
    pub(crate) pat: Rc<Pat>,
    pub(crate) expr: Rc<Expr>,
}

// pub(crate) type MatchArm = (Rc<Pat>, Rc<Expr>);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Pat {
    pub(crate) kind: Rc<PatKind>,
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for Pat {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.kind {
            PatKind::Wildcard => vec![],
            PatKind::Var(_) => vec![],
            PatKind::Unit => vec![],
            PatKind::Int(_) => vec![],
            PatKind::Float(_) => vec![],
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum PatKind {
    // EmptyHole,
    Wildcard,
    Var(Identifier),
    Variant(Identifier, Option<Rc<Pat>>),
    Unit,
    Int(i64),
    Float(String), // represented as String to allow Eq and Hash
    Bool(bool),
    Str(String),
    Tuple(Vec<Rc<Pat>>),
}

impl PatKind {
    pub(crate) fn get_identifier_of_variable(&self) -> Identifier {
        match self {
            PatKind::Var(id) => id.clone(),
            _ => {
                panic!("Pattern is not a variable")
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct AstType {
    pub(crate) typekind: Rc<TypeKind>,
    pub(crate) span: Span,
    pub(crate) id: NodeId,
}

impl Node for AstType {
    fn span(&self) -> Span {
        self.span.clone()
    }
    fn id(&self) -> NodeId {
        self.id
    }

    fn children(&self) -> Vec<Rc<dyn Node>> {
        match &*self.typekind {
            TypeKind::Poly(_, _)
            | TypeKind::Name(_)
            | TypeKind::Unit
            | TypeKind::Int
            | TypeKind::Float
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
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypeKind {
    Poly(Identifier, Vec<Identifier>),
    Name(Identifier),
    Ap(Identifier, Vec<Rc<AstType>>),
    Unit,
    Int,
    Float,
    Bool,
    Str,
    Function(Vec<Rc<AstType>>, Rc<AstType>),
    Tuple(Vec<Rc<AstType>>),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct NodeId {
    pub(crate) id: usize,
}

impl NodeId {
    pub(crate) fn new() -> Self {
        static ID_COUNTER: std::sync::atomic::AtomicUsize = AtomicUsize::new(1);
        let id = ID_COUNTER.fetch_add(1, Ordering::Relaxed);
        Self { id }
    }
}

impl std::fmt::Display for NodeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Id[{}]", self.id)
    }
}

impl Default for NodeId {
    fn default() -> Self {
        NodeId::new()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Span {
    pub(crate) filename: String,
    pub(crate) lo: usize,
    pub(crate) hi: usize,
}

impl Span {
    fn new(filename: &str, pest_span: pest::Span) -> Self {
        Span {
            filename: filename.to_string(),
            lo: pest_span.start(),
            hi: pest_span.end(),
        }
    }

    pub(crate) fn lines_and_columns(&self, source: &str) -> ((usize, usize), (usize, usize)) {
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

    pub(crate) fn display(&self, s: &mut String, sources: &Sources, detail: &str) {
        let source = sources.filename_to_source.get(&self.filename).unwrap();
        let ((lo_line, lo_col), (hi_line, hi_col)) = self.lines_and_columns(source);
        if lo_line != hi_line {
            s.push_str(&format!(
                "--> On lines {}-{} of {}, {}\n",
                lo_line + 1,
                hi_line + 1,
                self.filename,
                detail
            ));
        } else {
            s.push_str(&format!(
                "--> On line {} of {}, {}\n",
                lo_line + 1,
                self.filename,
                detail
            ));
        }
        for line_number in lo_line..=hi_line {
            let line = source.lines().nth(line_number).unwrap();
            s.push_str(&format!("{:3} | {}\n", line_number + 1, line));

            let pad_before = if line_number == lo_line { lo_col } else { 0 };
            let num_tabs = line.chars().take(pad_before).filter(|c| *c == '\t').count();
            let pad_before_in_spaces = pad_before + num_tabs * 3;

            let underline_length = if line_number == hi_line {
                hi_col - pad_before + 1
            } else {
                line.len() - pad_before
            };
            s.push_str(&format!("{:3} | ", "")); // line number placeholder
            s.push_str(&format!("{:1$}", "", pad_before_in_spaces)); // pad before
            s.push_str(&format!("{:^<1$}\n", "", underline_length)); // underline
        }
    }
}

pub(crate) fn get_pairs(source: &str) -> Result<Pairs<Rule>, String> {
    MyParser::parse(Rule::file, source).map_err(|e| e.to_string())
}

pub(crate) fn parse_func_arg_annotation(pair: Pair<Rule>, filename: &str) -> ArgAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::func_arg => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair, filename);
            let annot = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), filename));
            (pat, annot)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_annotated_let_pattern(pair: Pair<Rule>, filename: &str) -> PatAnnotated {
    let rule = pair.as_rule();
    match rule {
        Rule::let_pattern_annotated => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pat_pair = inner[0].clone();
            let pat = parse_let_pattern(pat_pair, filename);
            let ty = inner
                .get(1)
                .map(|type_pair| parse_type_term(type_pair.clone(), filename));
            (pat, ty)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_func_out_annotation(pair: Pair<Rule>, filename: &str) -> Rc<AstType> {
    let rule = pair.as_rule();
    match rule {
        Rule::func_out_annotation => {
            let inner: Vec<_> = pair.into_inner().collect();
            let type_pair = inner[0].clone();
            parse_type_term(type_pair, filename)
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_let_pattern(pair: Pair<Rule>, filename: &str) -> Rc<Pat> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_let_pattern(pair, filename)
        }
        Rule::identifier => Rc::new(Pat {
            kind: Rc::new(PatKind::Var(pair.as_str().to_owned())),
            span,
            id: NodeId::new(),
        }),
        Rule::wildcard => Rc::new(Pat {
            kind: Rc::new(PatKind::Wildcard),
            span,
            id: NodeId::new(),
        }),
        Rule::let_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_let_pattern(pair.clone(), filename))
                .collect();
            Rc::new(Pat {
                kind: Rc::new(PatKind::Tuple(pats)),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_match_pattern(pair: Pair<Rule>, filename: &str) -> Rc<Pat> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    match rule {
        Rule::match_pattern => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pair = inner.first().unwrap().clone();
            parse_match_pattern(pair, filename)
        }
        Rule::match_pattern_variable => Rc::new(Pat {
            kind: Rc::new(PatKind::Var(pair.as_str()[1..].to_owned())),
            span,
            id: NodeId::new(),
        }),
        Rule::match_pattern_tuple => {
            let inner: Vec<_> = pair.into_inner().collect();
            let pats = inner
                .iter()
                .map(|pair| parse_match_pattern(pair.clone(), filename))
                .collect();
            Rc::new(Pat {
                kind: Rc::new(PatKind::Tuple(pats)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::match_pattern_variant => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let pat = inner
                .get(1)
                .map(|pair| parse_match_pattern(pair.clone(), filename));
            Rc::new(Pat {
                kind: Rc::new(PatKind::Variant(name, pat)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::wildcard => Rc::new(Pat {
            kind: Rc::new(PatKind::Wildcard),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_unit => Rc::new(Pat {
            kind: Rc::new(PatKind::Unit),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_int => Rc::new(Pat {
            kind: Rc::new(PatKind::Int(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_float => Rc::new(Pat {
            kind: Rc::new(PatKind::Float(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_bool => Rc::new(Pat {
            kind: Rc::new(PatKind::Bool(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_string => Rc::new(Pat {
            kind: Rc::new(PatKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
            id: NodeId::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_type_term(pair: Pair<Rule>, filename: &str) -> Rc<AstType> {
    let span = Span::new(filename, pair.as_span());
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
                id: NodeId::new(),
            })
        }
        Rule::identifier => {
            let ident = pair.as_str().to_string();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Name(ident)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::type_literal_unit => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Unit),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_int => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Int),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_float => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Float),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_bool => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Bool),
            span,
            id: NodeId::new(),
        }),
        Rule::type_literal_string => Rc::new(AstType {
            typekind: Rc::new(TypeKind::Str),
            span,
            id: NodeId::new(),
        }),
        Rule::tuple_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let types = inner
                .into_iter()
                .map(|t| parse_type_term(t, filename))
                .collect();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Tuple(types)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::type_ap => {
            let inner: Vec<_> = pair.into_inner().collect();
            let name = inner[0].as_str().to_owned();
            let types = inner
                .into_iter()
                .skip(1)
                .map(|t| parse_type_term(t, filename))
                .collect();
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Ap(name, types)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::func_type => {
            let inner: Vec<_> = pair.into_inner().collect();
            let len = inner.len();
            let args: Vec<_> = inner
                .clone()
                .into_iter()
                .take(len - 1)
                .map(|t| parse_type_term(t, filename))
                .collect();
            let ret = parse_type_term(inner.last().unwrap().clone(), filename);
            Rc::new(AstType {
                typekind: Rc::new(TypeKind::Function(args, ret)),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", pair),
    }
}

pub(crate) fn parse_stmt(pair: Pair<Rule>, filename: &str) -> Rc<Stmt> {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::func_def => {
            let mut n = 0;
            let mut args = vec![];
            let name = parse_let_pattern(inner[0].clone(), filename);
            n += 1;
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), filename);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ret_type = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), filename))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::FuncDef(
                    FuncDef {
                        name,
                        args,
                        ret_type,
                        body,
                    }
                    .into(),
                )),
                span,
                id: NodeId::new(),
            })
        }
        Rule::let_statement => {
            let offset = 0;
            let pat_annotated = parse_annotated_let_pattern(inner[offset].clone(), filename);
            let expr = parse_expr_pratt(Pairs::single(inner[offset + 1].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Let(false, pat_annotated, expr)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::var_statement => {
            let offset = 0;
            let pat_annotated = parse_annotated_let_pattern(inner[offset].clone(), filename);
            let expr = parse_expr_pratt(Pairs::single(inner[offset + 1].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Let(true, pat_annotated, expr)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::set_statement => {
            let expr1 = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let expr2 = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Set(expr1, expr2)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::expression_statement => {
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::Expr(expr)),
                span,
                id: NodeId::new(),
            })
        }
        // Rule::typealias => {
        //     let ident = inner[0].as_str().to_string();
        //     let definition = parse_type_term(inner[1].clone(), filename);
        //     Rc::new(Stmt {
        //         kind: Rc::new(StmtKind::TypeDef(Rc::new(TypeDefKind::Alias(
        //             ident, definition,
        //         )))),
        //         span,
        //         id: NodeId::new(),
        //     })
        // }
        Rule::enum_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut ty_args = vec![];
            while let Rule::type_poly = inner[n].as_rule() {
                ty_args.push(parse_type_term(inner[n].clone(), filename));
                n += 1;
            }
            let mut variants = vec![];
            while let Some(pair) = inner.get(n) {
                let variant = parse_variant(pair.clone(), filename);
                variants.push(variant);
                n += 1;
            }
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::TypeDef(Rc::new(TypeDefKind::Enum(
                    EnumDef {
                        name,
                        ty_args,
                        variants,
                    }
                    .into(),
                )))),
                span,
                id: NodeId::new(),
            })
        }
        Rule::struct_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut ty_args = vec![];
            while let Rule::type_poly = inner[n].as_rule() {
                ty_args.push(parse_type_term(inner[n].clone(), filename));
                n += 1;
            }
            let mut fields = vec![];
            while let Some(pair) = inner.get(n) {
                let field = parse_struct_field(pair.clone(), filename);
                fields.push(Rc::new(field));
                n += 1;
            }
            Rc::new(Stmt {
                kind: Rc::new(StmtKind::TypeDef(Rc::new(TypeDefKind::Struct(
                    StructDef {
                        name,
                        ty_args,
                        fields,
                    }
                    .into(),
                )))),
                span,
                id: NodeId::new(),
            })
        }
        Rule::interface_declaration => {
            let name = inner[0].as_str().to_string();
            let mut n = 1;
            let mut props = vec![];
            while let Some(pair) = inner.get(n) {
                let method = parse_interface_method(pair.clone(), filename);
                props.push(Rc::new(method));
                n += 1;
            }
            Rc::new(Stmt {
                kind: StmtKind::InterfaceDef(InterfaceDef { name, props }.into()).into(),
                span,
                id: NodeId::new(),
            })
        }
        Rule::interface_implementation => {
            let ident = inner[0].as_str().to_string();
            let ty = parse_type_term(inner[1].clone(), filename);
            let mut n = 2;
            let mut stmts = vec![];
            while let Some(pair) = inner.get(n) {
                let stmt = parse_stmt(pair.clone(), filename);
                stmts.push(stmt);
                n += 1;
            }
            Rc::new(Stmt {
                kind: StmtKind::InterfaceImpl(ident, ty, stmts).into(),
                span,
                id: NodeId::new(),
            })
        }
        Rule::import => {
            let ident = inner[0].as_str().to_string();
            Rc::new(Stmt {
                kind: StmtKind::Import(ident).into(),
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_interface_method(pair: Pair<Rule>, filename: &str) -> InterfaceProperty {
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::interface_property => {
            let ident = inner[0].as_str().to_string();
            let ty = parse_type_term(inner[1].clone(), filename);
            InterfaceProperty { ident, ty }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_variant(pair: Pair<Rule>, filename: &str) -> Rc<Variant> {
    let span = Span::new(filename, pair.as_span());
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
                let data = parse_type_term(pair.clone(), filename);
                Some(data)
            } else {
                None
            };
            Rc::new(Variant {
                ctor: ident,
                data,
                span,
                id: NodeId::new(),
            })
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_struct_field(pair: Pair<Rule>, filename: &str) -> StructField {
    let span = Span::new(filename, pair.as_span());
    let rule = pair.as_rule();
    let inner: Vec<_> = pair.into_inner().collect();
    match rule {
        Rule::struct_field => {
            let ident = inner[0].as_str().to_string();
            let ty = parse_type_term(inner[1].clone(), filename);
            StructField {
                ident,
                ty,
                span,
                id: NodeId::new(),
            }
        }
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_expr_term(pair: Pair<Rule>, filename: &str) -> Rc<Expr> {
    let span = Span::new(filename, pair.as_span());
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
        Rule::expression => parse_expr_pratt(pair.into_inner(), filename),
        // All rules listed below should be non-operator expressions
        Rule::block_expression => {
            let inner = pair.into_inner();
            let mut statements: Vec<Rc<Stmt>> = Vec::new();
            for pair in inner {
                statements.push(parse_stmt(pair, filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Block(statements)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::if_else_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let e1 = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
            let e2 = if inner.len() == 3 {
                Some(parse_expr_pratt(Pairs::single(inner[2].clone()), filename))
            } else {
                None
            };
            Rc::new(Expr {
                kind: Rc::new(ExprKind::If(cond, e1, e2)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::while_loop_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let cond = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let e = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
            Rc::new(Expr {
                kind: Rc::new(ExprKind::WhileLoop(cond, e)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::match_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let expr = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let mut arms = vec![];
            fn parse_match_arm(pair: &Pair<Rule>, filename: &str) -> MatchArm {
                let inner: Vec<_> = pair.clone().into_inner().collect();
                let pat = parse_match_pattern(inner[0].clone(), filename);
                let expr = parse_expr_pratt(Pairs::single(inner[1].clone()), filename);
                MatchArm { pat, expr }
            }
            for pair in &inner[1..] {
                arms.push(parse_match_arm(pair, filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Match(expr, arms)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::func_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut n = 0;
            let mut args = vec![];
            while let Rule::func_arg = inner[n].as_rule() {
                let pat_annotated = parse_func_arg_annotation(inner[n].clone(), filename);
                args.push(pat_annotated);
                n += 1;
            }

            let maybe_func_out = &inner[n];
            let ty_out = match maybe_func_out.as_rule() {
                Rule::func_out_annotation => {
                    // n += 1;
                    Some(parse_func_out_annotation(maybe_func_out.clone(), filename))
                }
                _ => None,
            };
            let body = parse_expr_pratt(Pairs::single(inner.last().unwrap().clone()), filename);
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Func(args, ty_out, body)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::func_call_expression => {
            let inner: Vec<_> = pair.into_inner().collect();
            let f = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
            let inner: Vec<_> = inner[1].clone().into_inner().collect();
            let mut args = vec![];
            for p in &inner[0..] {
                args.push(parse_expr_pratt(Pairs::single(p.clone()), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::FuncAp(f, args)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::tuple_expr => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Tuple(exprs)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::literal_unit => Rc::new(Expr {
            kind: Rc::new(ExprKind::Unit),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_int => Rc::new(Expr {
            kind: Rc::new(ExprKind::Int(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_float => Rc::new(Expr {
            kind: Rc::new(ExprKind::Float(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_bool => Rc::new(Expr {
            kind: Rc::new(ExprKind::Bool(pair.as_str().parse().unwrap())),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_string => Rc::new(Expr {
            kind: Rc::new(ExprKind::Str({
                let s = pair.as_str();
                // remove quotes
                s[1..s.len() - 1].to_owned()
            })),
            span,
            id: NodeId::new(),
        }),
        Rule::literal_list => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::List(exprs)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::literal_array => {
            let inner: Vec<_> = pair.into_inner().collect();
            let mut exprs = vec![];
            for p in inner {
                exprs.push(parse_expr_pratt(Pairs::single(p), filename));
            }
            Rc::new(Expr {
                kind: Rc::new(ExprKind::Array(exprs)),
                span,
                id: NodeId::new(),
            })
        }
        Rule::identifier => Rc::new(Expr {
            kind: Rc::new(ExprKind::Identifier(pair.as_str().to_owned())),
            span,
            id: NodeId::new(),
        }),
        _ => panic!("unreachable rule {:#?}", rule),
    }
}

pub(crate) fn parse_file(pairs: Pairs<Rule>, filename: &str) -> Rc<FileAst> {
    let mut items = Vec::new();
    let pairs: Vec<_> = pairs.into_iter().collect();
    for pair in &pairs {
        if pair.as_rule() == Rule::EOI {
            break;
        }
        let stmt = parse_stmt(pair.clone(), filename);
        items.push(stmt)
    }
    let span1: Span = Span::new(filename, pairs.first().unwrap().as_span());
    let span2: Span = Span::new(filename, pairs.last().unwrap().as_span());
    Rc::new(FileAst {
        statements: items,
        // remove the .abra suffix from filename
        name: filename.to_string()[..filename.len() - 5].to_string(),
        span: Span {
            filename: filename.to_string(),
            lo: span1.lo,
            hi: span2.hi,
        },
        id: NodeId::new(),
    })
}

pub(crate) fn parse_expr_pratt(pairs: Pairs<Rule>, filename: &str) -> Rc<Expr> {
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
            | Op::infix(Rule::op_mod, Assoc::Left))
        .op(Op::infix(Rule::op_pow, Assoc::Left))
        .op(Op::infix(Rule::op_access, Assoc::Left))
        .op(Op::postfix(Rule::index_access));
    pratt
        .map_primary(|t| parse_expr_term(t, filename))
        .map_prefix(|_op, _rhs| panic!("prefix operator encountered"))
        .map_postfix(|lhs, op| match op.as_rule() {
            Rule::index_access => {
                let span = Span::new(filename, op.as_span());
                let inner: Vec<_> = op.into_inner().collect();
                let index = parse_expr_pratt(Pairs::single(inner[0].clone()), filename);
                Rc::new(Expr {
                    kind: Rc::new(ExprKind::IndexAccess(lhs, index)),
                    span,
                    id: NodeId::new(),
                })
            }
            _ => unreachable!(),
        })
        .map_infix(|lhs, op, rhs| {
            let opcode = match op.as_rule() {
                Rule::op_eq => Some(BinOpcode::Equal),
                Rule::op_gt => Some(BinOpcode::GreaterThan),
                Rule::op_lt => Some(BinOpcode::LessThan),
                Rule::op_gte => Some(BinOpcode::GreaterThanOrEqual),
                Rule::op_lte => Some(BinOpcode::LessThanOrEqual),
                Rule::op_addition => Some(BinOpcode::Add),
                Rule::op_subtraction => Some(BinOpcode::Subtract),
                Rule::op_multiplication => Some(BinOpcode::Multiply),
                Rule::op_division => Some(BinOpcode::Divide),
                Rule::op_pow => Some(BinOpcode::Pow),
                Rule::op_mod => Some(BinOpcode::Mod),
                Rule::op_and => Some(BinOpcode::And),
                Rule::op_or => Some(BinOpcode::Or),
                Rule::op_concat => Some(BinOpcode::Concat),
                _ => None,
            };
            match opcode {
                Some(opcode) => Rc::new(Expr {
                    kind: Rc::new(ExprKind::BinOp(lhs, opcode, rhs)),
                    span: Span::new(filename, op.as_span()),
                    id: NodeId::new(),
                }),
                None => Rc::new(Expr {
                    kind: Rc::new(ExprKind::MemberAccess(lhs, rhs)),
                    span: Span::new(filename, op.as_span()),
                    id: NodeId::new(),
                }),
            }
        })
        .parse(pairs)
}

pub(crate) fn parse_or_err(sources: &Vec<SourceFile>) -> Result<Vec<Rc<FileAst>>, String> {
    let mut files = vec![];
    for sf in sources {
        let pairs = get_pairs(&sf.contents)?;

        let file = parse_file(pairs, &sf.name);
        files.push(file);
    }
    Ok(files)
}

pub(crate) type NodeMap = HashMap<NodeId, Rc<dyn Node>>;

pub(crate) fn initialize_node_map(node_map: &mut NodeMap, node: &Rc<dyn Node>) {
    node_map.insert(node.id(), node.clone());
    for child in node.children() {
        initialize_node_map(node_map, &child);
    }
}
