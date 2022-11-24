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
    Block(Vec<Rc<Stmt>>, Option<Rc<Expr>>),
    BinOp(Rc<Expr>, BinOpcode, Rc<Expr>),
    FuncAp(Rc<Expr>, Rc<Expr>, Vec<Rc<Expr>>),
}

pub type Rule = (Rc<Pat>, Rc<Expr>);

#[derive(Debug, PartialEq)]
pub struct Pat {
    pub patkind: Rc<PatKind>,
    pub span: Span,
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

#[cfg(test)]
mod tests {
    use super::*;

    // #[test]
    // fn parse_unit() {
    //     let source = "()";
    //     let parse_tree = parse(source);
    //     let expected_parse_tree = Rc::new(Expr {
    //         exprkind: Rc::new(ExprKind::Unit),
    //         span: Span {
    //             lo: 0,
    //             hi: source.chars().count(),
    //         },
    //     });
    //     assert_eq!(parse_tree, expected_parse_tree);
    // }
}
