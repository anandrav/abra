#[derive(Debug)]
pub enum Expr {
    Var(String),
    Int(i32),
    BinOp(Box<Expr>, BinOpcode, Box<Expr>),
    Let(Box<Pat>, Option<Type>, Box<Expr>, Box<Expr>)
}

#[derive(Debug)]
pub enum Pat {
    Var(String)
}

#[derive(Debug)]
pub enum Type {
    Int
}

#[derive(Debug)]
pub enum BinOpcode {
    Semicolon,
    Add,
    Subtract,
    Multiply,
    Divide,
}