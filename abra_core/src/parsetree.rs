#[derive(Debug)]
pub enum Expr {
    Var(String),
    Unit,
    Int(i32),
    Bool(bool),
    BinOp(Box<Expr>, BinOpcode, Box<Expr>),
    Let(Box<Pat>, Option<Type>, Box<Expr>, Box<Expr>),
    If(Box<Expr>, Box<Expr>, Box<Expr>),
    Match(Box<Expr>, Vec<Rule>)
}

pub type Rule = (Box<Pat>, Box<Expr>);

#[derive(Debug)]
pub enum Pat {
    Var(String)
}

#[derive(Debug)]
pub enum Type {
    Unit,
    Int,
    Bool,
    String
}

#[derive(Debug)]
pub enum BinOpcode {
    Semicolon,
    Add,
    Subtract,
    Multiply,
    Divide,
}