use operators::BinOpcode;
use pest_derive::Parser;
use regex::Regex;
use std::collections::VecDeque;
use std::rc::Rc;
use types::Type;

#[derive(Parser)]
#[grammar = "grammar.pest"] // relative to src
struct MyParser;

pub type Identifier = String;
pub type FuncArg = (Identifier, Option<Rc<Type>>);

#[derive(Debug, PartialEq)]
pub enum Action {
    InsertChar { c: char, loc: usize },
    Backspace { loc: usize },
}

#[derive(Debug, PartialEq)]
pub enum Token {
    Space,
    Newline,
    Tab,
    OpenDelim(Delimiter),
    CloseDelim(Delimiter),
    Identifier(String),
}

impl ToString for Token {
    fn to_string(&self) -> String {
        unimplemented!()
    }
}

#[derive(Debug, PartialEq)]
pub enum TokenTree {
    Leaf(Token),
    Children(Vec<Rc<TokenTree>>),
}

#[derive(Debug, PartialEq)]
pub enum Delimiter {
    Parenthesis,
    Brace,
    Bracket,
}

#[derive(Debug, PartialEq)]
pub struct Stmt {
    pub stmtkind: StmtKind,
    // pub tokens: TokenTree,
}

#[derive(Debug, PartialEq)]
pub enum StmtKind {
    /// just a semicolon
    EmptyHole,
    Let(Rc<Pat>, Option<Rc<Type>>, Rc<Expr>, Rc<Expr>),
    Expr(Expr),
}

#[derive(Debug, PartialEq)]
pub struct Expr {
    pub exprkind: ExprKind,
    // pub tokens: TokenTree,
}

#[derive(Debug, PartialEq)]
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
    Block(VecDeque<Rc<Stmt>>),
    BinOp(Rc<Expr>, Operator, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, VecDeque<Rc<Expr>>),
}

#[derive(Debug, PartialEq)]
pub struct Pat {
    pub patkind: ExprKind,
    // pub tokens: TokenTree,
}

#[derive(Debug, PartialEq)]
pub enum PatKind {
    EmptyHole,
    InvalidText(String),
    Var(Identifier),
    Unit,
    Int(i32),
    Bool(bool),
    Str(String),
}
#[derive(Debug, PartialEq)]
pub enum Op {
    Operand(Rc<Expr>),
    Operator(Operator),
}

#[derive(Debug, PartialEq)]
pub enum Operator {
    EmptyHole,
    InvalidText(String),
    Valid(BinOpcode),
}

#[derive(Debug, PartialEq)]
pub enum CursorPosition {
    Before,
    After,
}

pub type CursorPositionText = usize;

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

fn is_identifier(text: &str) -> bool {
    let re = Regex::new(r"[a-zA-Z_.][.a-zA-Z_0-9']*(\.:[.+/*=-]+)?").unwrap();
    return re.is_match(text);
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn insert_int() {
        let emptyhole = Rc::new(Expr {
            exprkind: ExprKind::EmptyHole,
        });
        let num = emptyhole.perform_action(&Action::InsertChar { c: '2', loc: 0 });
        assert_eq!(emptyhole, num);
    }
}
