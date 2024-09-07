use crate::statics::{Monotype, SolvedType};

use once_cell::sync::Lazy;
use strum::IntoEnumIterator;
use strum_macros::EnumIter;

pub static BUILTINS: Lazy<Vec<Builtin>> = Lazy::new(Builtin::enumerate);

#[derive(Debug, Clone, PartialEq, Eq, EnumIter)]
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

    IntToString,
    FloatToString,

    ArrayAppend,
    ArrayLength,
    ArrayPop,
}

impl Builtin {
    fn name(&self) -> String {
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

            Builtin::IntToString => "int_to_string".into(),
            Builtin::FloatToString => "float_to_string".into(),

            Builtin::ArrayAppend => "array_append".into(),
            Builtin::ArrayLength => "array_length".into(),
            Builtin::ArrayPop => "array_pop".into(),
        }
    }

    fn type_signature(&self) -> SolvedType {
        match self {
            Builtin::AddInt
            | Builtin::SubtractInt
            | Builtin::MultiplyInt
            | Builtin::DivideInt
            | Builtin::ModuloInt
            | Builtin::PowerInt => SolvedType::Function(
                vec![SolvedType::Int, SolvedType::Int],
                Box::new(SolvedType::Int),
            ),
            Builtin::SqrtInt => {
                SolvedType::Function(vec![SolvedType::Int], Box::new(SolvedType::Int))
            }

            Builtin::AddFloat
            | Builtin::SubtractFloat
            | Builtin::MultiplyFloat
            | Builtin::DivideFloat
            | Builtin::ModuloFloat
            | Builtin::PowerFloat => SolvedType::Function(
                vec![SolvedType::Float, SolvedType::Float],
                Box::new(SolvedType::Float),
            ),
            Builtin::SqrtFloat => {
                SolvedType::Function(vec![SolvedType::Float], Box::new(SolvedType::Float))
            }

            Builtin::LessThanInt
            | Builtin::LessThanOrEqualInt
            | Builtin::GreaterThanInt
            | Builtin::GreaterThanOrEqualInt
            | Builtin::EqualInt => SolvedType::Function(
                vec![SolvedType::Int, SolvedType::Int],
                Box::new(SolvedType::Bool),
            ),

            Builtin::LessThanFloat
            | Builtin::LessThanOrEqualFloat
            | Builtin::GreaterThanFloat
            | Builtin::GreaterThanOrEqualFloat
            | Builtin::EqualFloat => SolvedType::Function(
                vec![SolvedType::Float, SolvedType::Float],
                Box::new(SolvedType::Bool),
            ),

            Builtin::IntToString => {
                SolvedType::Function(vec![SolvedType::Int], Box::new(SolvedType::String))
            }
            Builtin::FloatToString => {
                SolvedType::Function(vec![SolvedType::Float], Box::new(SolvedType::String))
            }

            Builtin::ArrayAppend => SolvedType::Function(
                vec![
                    SolvedType::UdtInstance(
                        "array".into(),
                        vec![SolvedType::Poly("a".to_string(), vec![])],
                    ),
                    SolvedType::Poly("a".to_string(), vec![]),
                ],
                Box::new(SolvedType::Unit),
            ),
            Builtin::ArrayLength => SolvedType::Function(
                vec![SolvedType::UdtInstance(
                    "array".into(),
                    vec![SolvedType::Poly("a".into(), vec![])],
                )],
                Box::new(SolvedType::Int),
            ),
            Builtin::ArrayPop => SolvedType::Function(
                vec![SolvedType::UdtInstance(
                    "array".into(),
                    vec![SolvedType::Poly("a".into(), vec![])],
                )],
                Box::new(SolvedType::Unit),
            ),
        }
    }

    fn enumerate() -> Vec<Self> {
        Self::iter().collect()
    }
}
