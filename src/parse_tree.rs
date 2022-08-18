use operators::BinOpcode;
use std::collections::VecDeque;
use std::rc::Rc;
use types::Type;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug)]
pub struct Span {
    pub lo: usize,
    pub hi: usize,
}

#[derive(Debug)]
pub struct Stmt {
    pub stmtkind: Rc<StmtKind>,
    pub span: Span,
}

#[derive(Debug)]
pub enum StmtKind {
    EmptyHole,
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>),
    Expr(Rc<Expr>),
}

#[derive(Debug)]
pub struct Expr {
    pub exprkind: Rc<ExprKind>,
    pub span: Span,
}

#[derive(Debug)]
pub enum ExprKind {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
    Func(FuncArg, Vec<FuncArg>, Option<Rc<Type>>, Rc<Expr>),
    If(Rc<Expr>, Rc<Expr>, Rc<Expr>),
    Match(Rc<Expr>, Vec<Rule>),
    Block(VecDeque<Rc<Stmt>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, VecDeque<Rc<Expr>>),
}

pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug)]
pub struct Pat {
    pub patkind: Rc<PatKind>,
    pub span: Span,
}

#[derive(Debug)]
pub enum PatKind {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
}

// macro_rules! vecdeque {
//     () => (
//         VecDeque::new()
//     );
//     ($elem:expr; $n:expr) => (
//         $crate::vec::from_elem($elem, $n).to_iter().collect()
//     );
//     ($($x:expr),*) => (
//         $crate::slice::into_vec(box [$($x),*]).to_iter().collect()
//     );
//     ($($x:expr,)*) => (vec![$($x),*].to_iter().collect())
// }
