#[derive(Debug, Copy, Clone, PartialEq)]
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
