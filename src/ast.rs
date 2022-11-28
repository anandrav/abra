use operators::BinOpcode;
use std::rc::Rc;
use types::Type;
lalrpop_mod!(pub abra_grammar); // synthesized by LALRPOP

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

pub fn parse(source: &str) -> Result<Rc<Expr>, String> {
    abra_grammar::ExprParser::new()
        .parse(source)
        .map_err(|err| err.to_string())
}

#[derive(Debug, PartialEq)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
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
