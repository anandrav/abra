/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::statics::typecheck::Reason;
use crate::statics::typecheck::TypeVar;
use crate::statics::typecheck::{Nominal, TypeKey};

use crate::statics::PolytypeDeclaration;
use heck::ToSnakeCase;
use strum::AsRefStr;
use strum::IntoEnumIterator;
use strum::VariantArray;
use strum_macros::EnumIter;

#[derive(
    Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter, VariantArray, AsRefStr,
)]
pub enum IntrinsicOperation {
    // num operations
    AddInt,
    SubtractInt,
    MultiplyInt,
    DivideInt,
    PowerInt,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    DivideFloat,
    PowerFloat,

    // int operations
    Modulo,
    BitXor,
    WrappingAdd,
    WrappingMul,

    // float operations
    Ceil,
    Floor,
    Round,
    Sqrt,
    Sin,
    Cos,
    Tan,
    Asin,
    Acos,
    Atan,
    Log,
    Log2,
    Log10,

    Atan2,

    // TODO: maybe need atan2, exp aka e^x ?, is_nan(), is_inf(), is_neg_inf(),
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

    IntToFloat,
    FloatToInt,
    IntToString,
    FloatToString,

    ConcatStrings,
    StringNthByte,
    StringCountBytes,

    ArrayPush,
    ArrayLength,
    ArrayPop,

    Panic,
}

impl IntrinsicOperation {
    pub(crate) fn enumerate() -> Vec<Self> {
        Self::iter().collect()
    }

    pub(crate) fn name(&self) -> String {
        self.as_ref().to_snake_case()
    }

    pub(crate) fn type_signature(&self) -> TypeVar {
        let reason = Reason::Intrinsic(*self);
        match self {
            IntrinsicOperation::AddInt
            | IntrinsicOperation::SubtractInt
            | IntrinsicOperation::MultiplyInt
            | IntrinsicOperation::DivideInt
            | IntrinsicOperation::Modulo
            | IntrinsicOperation::BitXor
            | IntrinsicOperation::WrappingAdd
            | IntrinsicOperation::WrappingMul
            | IntrinsicOperation::PowerInt => TypeVar::make_func(
                vec![
                    TypeVar::make_int(reason.clone()),
                    TypeVar::make_int(reason.clone()),
                ],
                TypeVar::make_int(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::AddFloat
            | IntrinsicOperation::SubtractFloat
            | IntrinsicOperation::MultiplyFloat
            | IntrinsicOperation::DivideFloat
            | IntrinsicOperation::PowerFloat
            | IntrinsicOperation::Atan2 => TypeVar::make_func(
                vec![
                    TypeVar::make_float(reason.clone()),
                    TypeVar::make_float(reason.clone()),
                ],
                TypeVar::make_float(reason.clone()),
                reason.clone(),
            ),
            IntrinsicOperation::Ceil
            | IntrinsicOperation::Floor
            | IntrinsicOperation::Round
            | IntrinsicOperation::Sqrt
            | IntrinsicOperation::Sin
            | IntrinsicOperation::Cos
            | IntrinsicOperation::Tan
            | IntrinsicOperation::Asin
            | IntrinsicOperation::Acos
            | IntrinsicOperation::Atan
            | IntrinsicOperation::Log
            | IntrinsicOperation::Log2
            | IntrinsicOperation::Log10 => TypeVar::make_func(
                vec![TypeVar::make_float(reason.clone())],
                TypeVar::make_float(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::LessThanInt
            | IntrinsicOperation::LessThanOrEqualInt
            | IntrinsicOperation::GreaterThanInt
            | IntrinsicOperation::GreaterThanOrEqualInt
            | IntrinsicOperation::EqualInt => TypeVar::make_func(
                vec![
                    TypeVar::make_int(reason.clone()),
                    TypeVar::make_int(reason.clone()),
                ],
                TypeVar::make_bool(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::LessThanFloat
            | IntrinsicOperation::LessThanOrEqualFloat
            | IntrinsicOperation::GreaterThanFloat
            | IntrinsicOperation::GreaterThanOrEqualFloat
            | IntrinsicOperation::EqualFloat => TypeVar::make_func(
                vec![
                    TypeVar::make_float(reason.clone()),
                    TypeVar::make_float(reason.clone()),
                ],
                TypeVar::make_bool(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::EqualString => TypeVar::make_func(
                vec![
                    TypeVar::make_string(reason.clone()),
                    TypeVar::make_string(reason.clone()),
                ],
                TypeVar::make_bool(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::IntToFloat => TypeVar::make_func(
                vec![TypeVar::make_int(reason.clone())],
                TypeVar::make_float(reason.clone()),
                reason.clone(),
            ),
            IntrinsicOperation::FloatToInt => TypeVar::make_func(
                vec![TypeVar::make_float(reason.clone())],
                TypeVar::make_int(reason.clone()),
                reason.clone(),
            ),
            IntrinsicOperation::IntToString => TypeVar::make_func(
                vec![TypeVar::make_int(reason.clone())],
                TypeVar::make_string(reason.clone()),
                reason.clone(),
            ),
            IntrinsicOperation::FloatToString => TypeVar::make_func(
                vec![TypeVar::make_float(reason.clone())],
                TypeVar::make_string(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::ConcatStrings => TypeVar::make_func(
                vec![
                    TypeVar::make_string(reason.clone()),
                    TypeVar::make_string(reason.clone()),
                ],
                TypeVar::make_string(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::StringNthByte => TypeVar::make_func(
                vec![
                    TypeVar::make_string(reason.clone()),
                    TypeVar::make_int(reason.clone()),
                ],
                TypeVar::make_int(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::StringCountBytes => TypeVar::make_func(
                vec![TypeVar::make_string(reason.clone())],
                TypeVar::make_int(reason.clone()),
                reason.clone(),
            ),

            IntrinsicOperation::ArrayPush => {
                let a = TypeVar::make_poly(
                    reason.clone(),
                    PolytypeDeclaration::IntrinsicOperation(*self, "a".to_string()), // TODO: rename this and others to "T"
                );
                TypeVar::make_func(
                    vec![
                        TypeVar::make_nominal(reason.clone(), Nominal::Array, vec![a.clone()]),
                        a.clone(),
                    ],
                    TypeVar::make_void(reason.clone()),
                    reason.clone(),
                )
            }

            IntrinsicOperation::ArrayLength => {
                let a = TypeVar::make_poly(
                    reason.clone(),
                    PolytypeDeclaration::IntrinsicOperation(*self, "a".to_string()),
                );
                TypeVar::make_func(
                    vec![TypeVar::make_nominal(
                        reason.clone(),
                        Nominal::Array,
                        vec![a.clone()],
                    )],
                    TypeVar::make_int(reason.clone()),
                    reason.clone(),
                )
            }

            IntrinsicOperation::ArrayPop => {
                let a = TypeVar::make_poly(
                    reason.clone(),
                    PolytypeDeclaration::IntrinsicOperation(*self, "a".to_string()),
                );
                TypeVar::make_func(
                    vec![TypeVar::make_nominal(
                        reason.clone(),
                        Nominal::Array,
                        vec![a.clone()],
                    )],
                    a.clone(),
                    reason.clone(),
                )
            }

            IntrinsicOperation::Panic => TypeVar::make_func(
                vec![TypeVar::make_string(reason.clone())],
                TypeVar::make_never(reason.clone()),
                reason.clone(),
            ),
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum BuiltinType {
    Int,
    Bool,
    Float,
    Void,
    String,
    Tuple(u8),
}

impl BuiltinType {
    pub fn name(&self) -> &str {
        match self {
            Self::Int => "int",
            Self::Bool => "bool",
            Self::Float => "float",
            Self::Void => "void",
            Self::String => "string",
            Self::Tuple(_) => "tuple",
        }
    }

    pub fn to_type_key(self) -> TypeKey {
        match self {
            Self::Int => TypeKey::Int,
            Self::Bool => TypeKey::Bool,
            Self::Float => TypeKey::Float,
            Self::Void => TypeKey::Void,
            Self::String => TypeKey::String,
            Self::Tuple(arity) => TypeKey::Tuple(arity),
        }
    }
}
