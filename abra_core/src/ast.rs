#[derive(Debug)]
pub enum Expr {
    Int(i32),
    BinOp(Box<Expr>, BinOpcode, Box<Expr>),
}

#[derive(Debug)]
pub enum BinOpcode {
    Semicolon,
    Add,
    Subtract,
    Multiply,
    Divide,
}