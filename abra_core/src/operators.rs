#[derive(Debug, Copy, Clone)]
pub enum BinOpcode {
    Semicolon,
    Equals,
    LessThan,
    LessThanOrEquals,
    GreaterThan,
    GreaterThanOrEquals,
    Add,
    Subtract,
    Multiply,
    Divide,
}
