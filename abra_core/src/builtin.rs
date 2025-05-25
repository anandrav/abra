/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::statics::typecheck::Nominal;
use crate::statics::typecheck::Reason;
use crate::statics::typecheck::TypeVar;

use heck::ToSnakeCase;
use strum::AsRefStr;
use strum::IntoEnumIterator;
use strum::VariantArray;
use strum_macros::EnumIter;
// A Builtin is a function or constant built into the language
// It should either be something the user can't define themselves, or something that would be too expensive to express in the language
// For instance, the user cannot implement integer addition themselves (if there were no builtins at all)
// Another example: The user could implement sqrt(), but it's much faster to have it as a builtin

#[derive(
    Debug, Copy, Clone, PartialEq, Eq, Hash, PartialOrd, Ord, EnumIter, VariantArray, AsRefStr,
)]
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

    ArrayPush,
    ArrayLength,
    ArrayPop,

    Panic,

    // TODO: add support for "\n" in source, then remove this
    Newline,
}

impl Builtin {
    pub(crate) fn enumerate() -> Vec<Self> {
        Self::iter().collect()
    }

    pub(crate) fn name(&self) -> String {
        self.as_ref().to_snake_case()
    }

    pub(crate) fn type_signature(&self) -> TypeVar {
        let reason = Reason::Builtin(*self);
        match self {
            Builtin::AddInt
            | Builtin::SubtractInt
            | Builtin::MultiplyInt
            | Builtin::DivideInt
            | Builtin::ModuloInt
            | Builtin::PowerInt => TypeVar::make_func(
                vec![
                    TypeVar::make_int(reason.clone()),
                    TypeVar::make_int(reason.clone()),
                ],
                TypeVar::make_int(reason.clone()),
                reason.clone(),
            ),
            Builtin::SqrtInt => TypeVar::make_func(
                vec![TypeVar::make_int(reason.clone())],
                TypeVar::make_int(reason.clone()),
                reason.clone(),
            ),

            Builtin::AddFloat
            | Builtin::SubtractFloat
            | Builtin::MultiplyFloat
            | Builtin::DivideFloat
            | Builtin::ModuloFloat
            | Builtin::PowerFloat => TypeVar::make_func(
                vec![
                    TypeVar::make_float(reason.clone()),
                    TypeVar::make_float(reason.clone()),
                ],
                TypeVar::make_float(reason.clone()),
                reason.clone(),
            ),
            Builtin::SqrtFloat => TypeVar::make_func(
                vec![TypeVar::make_float(reason.clone())],
                TypeVar::make_float(reason.clone()),
                reason.clone(),
            ),

            Builtin::LessThanInt
            | Builtin::LessThanOrEqualInt
            | Builtin::GreaterThanInt
            | Builtin::GreaterThanOrEqualInt
            | Builtin::EqualInt => TypeVar::make_func(
                vec![
                    TypeVar::make_int(reason.clone()),
                    TypeVar::make_int(reason.clone()),
                ],
                TypeVar::make_bool(reason.clone()),
                reason.clone(),
            ),

            Builtin::LessThanFloat
            | Builtin::LessThanOrEqualFloat
            | Builtin::GreaterThanFloat
            | Builtin::GreaterThanOrEqualFloat
            | Builtin::EqualFloat => TypeVar::make_func(
                vec![
                    TypeVar::make_float(reason.clone()),
                    TypeVar::make_float(reason.clone()),
                ],
                TypeVar::make_bool(reason.clone()),
                reason.clone(),
            ),

            Builtin::EqualString => TypeVar::make_func(
                vec![
                    TypeVar::make_string(reason.clone()),
                    TypeVar::make_string(reason.clone()),
                ],
                TypeVar::make_bool(reason.clone()),
                reason.clone(),
            ),

            Builtin::IntToString => TypeVar::make_func(
                vec![TypeVar::make_int(reason.clone())],
                TypeVar::make_string(reason.clone()),
                reason.clone(),
            ),
            Builtin::FloatToString => TypeVar::make_func(
                vec![TypeVar::make_float(reason.clone())],
                TypeVar::make_string(reason.clone()),
                reason.clone(),
            ),

            Builtin::ConcatStrings => TypeVar::make_func(
                vec![
                    TypeVar::make_string(reason.clone()),
                    TypeVar::make_string(reason.clone()),
                ],
                TypeVar::make_string(reason.clone()),
                reason.clone(),
            ),

            Builtin::ArrayPush => {
                let a = TypeVar::empty();
                TypeVar::make_func(
                    vec![
                        TypeVar::make_nominal(reason.clone(), Nominal::Array, vec![a.clone()]),
                        a.clone(),
                    ],
                    TypeVar::make_unit(reason.clone()),
                    reason.clone(),
                )
            }

            Builtin::ArrayLength => {
                let a = TypeVar::empty();
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

            Builtin::ArrayPop => {
                let a = TypeVar::empty();
                TypeVar::make_func(
                    vec![TypeVar::make_nominal(
                        reason.clone(),
                        Nominal::Array,
                        vec![a.clone()],
                    )],
                    TypeVar::make_unit(reason.clone()),
                    reason.clone(),
                )
            }

            Builtin::Panic => TypeVar::make_func(
                vec![TypeVar::make_string(reason.clone())],
                TypeVar::make_never(reason.clone()),
                reason.clone(),
            ),

            Builtin::Newline => TypeVar::make_string(reason.clone()),
        }
    }
}
