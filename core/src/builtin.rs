use crate::statics::typecheck::Nominal;
use crate::statics::Type;

use strum::IntoEnumIterator;
use strum::VariantArray;
use strum_macros::EnumIter;

// A Builtin is a function or constant built into the language
// It should either be something the user can't define themselves, or something that would be too expensive to express in the language
// For instance, the user cannot implement integer addition themselves (if there were no builtins at all)
// Another example: The user could implement sqrt(), but it's much faster to have it as a builtin

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter, VariantArray)]
pub enum Builtin {
    AddInt,
    SubtractInt,
    MultiplyInt,
    DivideInt,
    ModuloInt,
    PowerInt,
    SqrtInt,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    DivideFloat,
    ModuloFloat,
    PowerFloat,
    SqrtFloat,

    LessThanInt,
    LessThanOrEqualInt,
    GreaterThanInt,
    GreaterThanOrEqualInt,

    LessThanFloat,
    LessThanOrEqualFloat,
    GreaterThanFloat,
    GreaterThanOrEqualFloat,

    EqualInt,
    EqualFloat,
    EqualString,

    IntToString,
    FloatToString,

    ConcatStrings,

    ArrayAppend,
    ArrayLength,
    ArrayPop,

    // TODO: add support for "\n" in source, then remove this
    Newline,
}

impl Builtin {
    pub(crate) fn enumerate() -> Vec<Self> {
        Self::iter().collect()
    }

    // TODO: use derive macro from Strum for this
    pub(crate) fn name(&self) -> String {
        match self {
            Builtin::AddInt => "add_int".into(),
            Builtin::SubtractInt => "subtract_int".into(),
            Builtin::MultiplyInt => "multiply_int".into(),
            Builtin::DivideInt => "divide_int".into(),
            Builtin::ModuloInt => "modulo_int".into(),
            Builtin::PowerInt => "power_int".into(),
            Builtin::SqrtInt => "sqrt_int".into(),

            Builtin::AddFloat => "add_float".into(),
            Builtin::SubtractFloat => "subtract_float".into(),
            Builtin::MultiplyFloat => "multiply_float".into(),
            Builtin::DivideFloat => "divide_float".into(),
            Builtin::ModuloFloat => "modulo_float".into(),
            Builtin::PowerFloat => "power_float".into(),
            Builtin::SqrtFloat => "sqrt_float".into(),

            Builtin::LessThanInt => "less_than_int".into(),
            Builtin::LessThanOrEqualInt => "less_than_or_equal_int".into(),
            Builtin::GreaterThanInt => "greater_than_int".into(),
            Builtin::GreaterThanOrEqualInt => "greater_than_or_equal_int".into(),

            Builtin::LessThanFloat => "less_than_float".into(),
            Builtin::LessThanOrEqualFloat => "less_than_or_equal_float".into(),
            Builtin::GreaterThanFloat => "greater_than_float".into(),
            Builtin::GreaterThanOrEqualFloat => "greater_than_or_equal_float".into(),

            Builtin::EqualInt => "equal_int".into(),
            Builtin::EqualFloat => "equal_float".into(),
            Builtin::EqualString => "equal_string".into(),

            Builtin::IntToString => "int_to_string".into(),
            Builtin::FloatToString => "float_to_string".into(),

            Builtin::ConcatStrings => "concat_strings".into(),

            Builtin::ArrayAppend => "array_append".into(),
            Builtin::ArrayLength => "array_length".into(),
            Builtin::ArrayPop => "array_pop".into(),

            Builtin::Newline => "newline".into(),
        }
    }

    pub(crate) fn type_signature(&self) -> Type {
        match self {
            Builtin::AddInt
            | Builtin::SubtractInt
            | Builtin::MultiplyInt
            | Builtin::DivideInt
            | Builtin::ModuloInt
            | Builtin::PowerInt => Type::Function(vec![Type::Int, Type::Int], Type::Int.into()),
            Builtin::SqrtInt => Type::Function(vec![Type::Int], Type::Int.into()),

            Builtin::AddFloat
            | Builtin::SubtractFloat
            | Builtin::MultiplyFloat
            | Builtin::DivideFloat
            | Builtin::ModuloFloat
            | Builtin::PowerFloat => {
                Type::Function(vec![Type::Float, Type::Float], Type::Float.into())
            }
            Builtin::SqrtFloat => Type::Function(vec![Type::Float], Type::Float.into()),

            Builtin::LessThanInt
            | Builtin::LessThanOrEqualInt
            | Builtin::GreaterThanInt
            | Builtin::GreaterThanOrEqualInt
            | Builtin::EqualInt => Type::Function(vec![Type::Int, Type::Int], Type::Bool.into()),

            Builtin::LessThanFloat
            | Builtin::LessThanOrEqualFloat
            | Builtin::GreaterThanFloat
            | Builtin::GreaterThanOrEqualFloat
            | Builtin::EqualFloat => {
                Type::Function(vec![Type::Float, Type::Float], Type::Bool.into())
            }

            Builtin::EqualString => {
                Type::Function(vec![Type::String, Type::String], Type::Bool.into())
            }

            Builtin::IntToString => Type::Function(vec![Type::Int], Type::String.into()),
            Builtin::FloatToString => Type::Function(vec![Type::Float], Type::String.into()),

            Builtin::ConcatStrings => {
                Type::Function(vec![Type::String, Type::String], Type::String.into())
            }

            Builtin::ArrayAppend => Type::Function(
                vec![
                    Type::Nominal(Nominal::Array, vec![Type::Poly("a".to_string(), vec![])]),
                    Type::Poly("a".to_string(), vec![]),
                ],
                Type::Unit.into(),
            ),

            Builtin::ArrayLength => Type::Function(
                vec![Type::Nominal(
                    Nominal::Array,
                    vec![Type::Poly("a".into(), vec![])],
                )],
                Type::Int.into(),
            ),

            Builtin::ArrayPop => Type::Function(
                vec![Type::Nominal(
                    Nominal::Array,
                    vec![Type::Poly("a".into(), vec![])],
                )],
                Type::Unit.into(),
            ),

            Builtin::Newline => Type::String,
        }
    }
}
