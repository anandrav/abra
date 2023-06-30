#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub enum BinOpcode {
    // comparison
    Equals,
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    // numeric
    Add,
    Subtract,
    Multiply,
    Divide,
    Mod,
    // boolean
    And,
    Or,
    // string
    Concat,
}
