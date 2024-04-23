#[derive(Debug, Copy, Clone, Hash, PartialEq, Eq)]
pub(crate) enum BinOpcode {
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
    Pow,
    // boolean
    And,
    Or,
    // string
    Concat,
}
