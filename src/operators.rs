#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum BinOpcode {
    // Semicolon,
    Equals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Add,
    Subtract,
    Multiply,
    Divide,
}
