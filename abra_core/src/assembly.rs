/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::translate_bytecode::{LabelMap, Translator, TranslatorState};
use crate::vm::{Instr as VmInstr, ProgramCounter};
use std::fmt::{self, Display, Formatter};
use utils::hash::HashMap;
use utils::id_set::IdSet;

pub(crate) type Label = String;

#[derive(Debug, Clone)]
pub(crate) enum Line {
    Instr {
        instr: Instr,
        lineno: usize,
        file_id: u32,
        func_id: u32,
    },
    Label(Label),
}

pub(crate) trait LineVariant {
    fn to_line(self, translator: &Translator, translator_state: &TranslatorState) -> Line;
}

impl LineVariant for Line {
    // TODO: remove translator argument if not needed
    fn to_line(self, _translator: &Translator, _st: &TranslatorState) -> Line {
        self
    }
}

impl LineVariant for Label {
    fn to_line(self, _translator: &Translator, _st: &TranslatorState) -> Line {
        Line::Label(self)
    }
}

impl LineVariant for Instr {
    fn to_line(self, _translator: &Translator, st: &TranslatorState) -> Line {
        Line::Instr {
            instr: self,
            lineno: st.curr_lineno,
            file_id: st.curr_file,
            func_id: st.curr_func,
        }
    }
}

impl Display for Line {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Line::Instr { instr, .. } => write!(f, "\t{instr}"),
            Line::Label(label) => write!(f, "{label}:"),
        }
    }
}

pub type Instr = VmInstr<Label, String>;

pub(crate) fn remove_labels(
    items: &Vec<Line>,
    string_constants: &IdSet<String>,
) -> (Vec<VmInstr>, LabelMap) {
    let mut instructions: Vec<VmInstr> = vec![];
    let mut offset = 0;
    let mut label_to_idx: LabelMap = HashMap::default();
    for item in items.iter() {
        match item {
            Line::Instr { .. } => {
                offset += 1;
            }
            Line::Label(label) => {
                label_to_idx.insert(label.clone(), offset);
            }
        }
    }
    // dbg!(&label_to_idx);

    for item in items {
        if let Line::Instr { instr, .. } = item {
            instructions.push(instr_to_vminstr(instr, &label_to_idx, string_constants));
        }
    }

    (instructions, label_to_idx)
}

fn _get_label(s: &str) -> Option<String> {
    if s.ends_with(":") {
        Some(s[0..s.len() - 1].into())
    } else {
        None
    }
}

fn instr_to_vminstr(
    instr: &Instr,
    label_to_idx: &HashMap<Label, usize>,
    string_constants: &IdSet<String>,
) -> VmInstr {
    match instr {
        Instr::Pop => VmInstr::Pop,
        Instr::Duplicate => VmInstr::Duplicate,
        Instr::LoadOffset(i) => VmInstr::LoadOffset(*i),
        Instr::StoreOffset(i) => VmInstr::StoreOffset(*i),
        Instr::AddInt => VmInstr::AddInt,
        Instr::SubtractInt => VmInstr::SubtractInt,
        Instr::MultiplyInt => VmInstr::MultiplyInt,
        Instr::DivideInt => VmInstr::DivideInt,
        Instr::PowerInt => VmInstr::PowerInt,
        Instr::Modulo => VmInstr::Modulo,
        Instr::AddFloat => VmInstr::AddFloat,
        Instr::SubtractFloat => VmInstr::SubtractFloat,
        Instr::MultiplyFloat => VmInstr::MultiplyFloat,
        Instr::DivideFloat => VmInstr::DivideFloat,
        Instr::PowerFloat => VmInstr::PowerFloat,
        Instr::SquareRoot => VmInstr::SquareRoot,
        Instr::Not => VmInstr::Not,
        Instr::And => VmInstr::And,
        Instr::Or => VmInstr::Or,
        Instr::LessThanInt => VmInstr::LessThanInt,
        Instr::LessThanOrEqualInt => VmInstr::LessThanOrEqualInt,
        Instr::GreaterThanInt => VmInstr::GreaterThanInt,
        Instr::GreaterThanOrEqualInt => VmInstr::GreaterThanOrEqualInt,
        Instr::LessThanFloat => VmInstr::LessThanFloat,
        Instr::LessThanOrEqualFloat => VmInstr::LessThanOrEqualFloat,
        Instr::GreaterThanFloat => VmInstr::GreaterThanFloat,
        Instr::GreaterThanOrEqualFloat => VmInstr::GreaterThanOrEqualFloat,
        Instr::EqualInt => VmInstr::EqualInt,
        Instr::EqualFloat => VmInstr::EqualFloat,
        Instr::EqualBool => VmInstr::EqualBool,
        Instr::EqualString => VmInstr::EqualString,
        Instr::PushNil(n) => VmInstr::PushNil(*n),
        Instr::PushBool(b) => VmInstr::PushBool(*b),
        Instr::PushInt(i) => VmInstr::PushInt(*i),
        Instr::PushFloat(f) => VmInstr::PushFloat(*f),
        Instr::PushString(s) => VmInstr::PushString(string_constants.try_get_id(s).unwrap() as u16),
        Instr::Jump(label) => VmInstr::Jump(ProgramCounter::new(label_to_idx[label])),
        Instr::JumpIf(label) => VmInstr::JumpIf(ProgramCounter::new(label_to_idx[label])),
        Instr::Call(nargs, label) => VmInstr::Call(
            *nargs,
            ProgramCounter::new(
                *label_to_idx
                    .get(label)
                    .unwrap_or_else(|| panic!("Could not find label: {label}")),
            ),
        ),
        Instr::CallExtern(func_id) => VmInstr::CallExtern(*func_id),
        Instr::CallFuncObj => VmInstr::CallFuncObj,
        Instr::Return => VmInstr::Return,
        Instr::Stop => VmInstr::Stop,
        Instr::Panic => VmInstr::Panic,
        Instr::ConstructStruct(n) => VmInstr::ConstructStruct(*n),
        Instr::ConstructArray(n) => VmInstr::ConstructArray(*n),
        Instr::DeconstructStruct => VmInstr::DeconstructStruct,
        Instr::DeconstructArray => VmInstr::DeconstructArray,
        Instr::DeconstructVariant => VmInstr::DeconstructVariant,
        Instr::GetField(idx) => VmInstr::GetField(*idx),
        Instr::SetField(idx) => VmInstr::SetField(*idx),
        Instr::GetIdx => VmInstr::GetIdx,
        Instr::SetIdx => VmInstr::SetIdx,
        Instr::ConstructVariant { tag } => VmInstr::ConstructVariant { tag: *tag },
        Instr::MakeClosure { func_addr } => {
            // dbg!(func_addr);
            VmInstr::MakeClosure {
                func_addr: ProgramCounter::new(label_to_idx[func_addr]),
            }
        }
        Instr::ArrayAppend => VmInstr::ArrayAppend,
        Instr::ArrayLength => VmInstr::ArrayLength,
        Instr::ArrayPop => VmInstr::ArrayPop,
        Instr::ConcatStrings => VmInstr::ConcatStrings,
        Instr::IntToString => VmInstr::IntToString,
        Instr::FloatToString => VmInstr::FloatToString,
        Instr::HostFunc(n) => VmInstr::HostFunc(*n),

        Instr::LoadLib => VmInstr::LoadLib,
        Instr::LoadForeignFunc => VmInstr::LoadForeignFunc,
    }
}

// fn _assemble_instr_or_label(
//     words: Vec<&str>,
//     lineno: usize,
//     string_constants: &mut IdSet<String>,
// ) -> Line {
//     if let Some(label) = _get_label(words[0]) {
//         return Line::Label(label);
//     }
//     let radix = 10;
//     let instr = match words[0] {
//         "pop" => Instr::Pop,
//         "loadoffset" => {
//             let n = i32::from_str_radix(words[1], radix).unwrap();
//             Instr::LoadOffset(n)
//         }
//         "storeoffset" => {
//             let n = i32::from_str_radix(words[1], radix).unwrap();
//             Instr::StoreOffset(n)
//         }
//         "add_int" => Instr::AddInt,
//         "subtract_int" => Instr::SubtractInt,
//         "multiply_int" => Instr::MultiplyInt,
//         "divide_int" => Instr::DivideInt,
//         "not" => Instr::Not,
//         "return" => Instr::Return,
//         "push_nil" => Instr::PushNil,
//         "push_bool" => {
//             let b = if words[1] == "true" {
//                 true
//             } else if words[1] == "false" {
//                 false
//             } else {
//                 panic!("On line {}, could not parse bool: {}", lineno, words[1]);
//             };
//             Instr::PushBool(b)
//         }
//         "push_int" => {
//             let n = i64::from_str_radix(words[1], radix).unwrap();
//             Instr::PushInt(n)
//         }
//         "push_string" => {
//             // remove quotes
//             let s = words[1][1..words[1].len() - 1].to_owned();
//             string_constants.insert(s.clone());
//             Instr::PushString(s)
//         }
//         "jump" | "jump_if" | "call" => {
//             let loc = words[1].into();
//             match words[0] {
//                 "jump" => Instr::Jump(loc),
//                 "jumpif" => Instr::JumpIf(loc),
//                 "call" => Instr::Call(loc),
//                 _ => unreachable!(),
//             }
//         }
//         "construct" => {
//             let n = u16::from_str_radix(words[1], radix).unwrap();
//             Instr::Construct(n)
//         }
//         "deconstruct" => Instr::Deconstruct,
//         "get_field" => {
//             let n = u16::from_str_radix(words[1], radix).unwrap();
//             Instr::GetField(n)
//         }
//         "set_field" => {
//             let n = u16::from_str_radix(words[1], radix).unwrap();
//             Instr::SetField(n)
//         }
//         "get_index" => Instr::GetIdx,
//         "set_index" => Instr::SetIdx,
//         "construct_variant" => {
//             let tag = u16::from_str_radix(words[1], radix).unwrap();
//             Instr::ConstructVariant { tag }
//         }
//         "call_host" => {
//             let n = u16::from_str_radix(words[1], radix).unwrap();
//             Instr::HostFunc(n)
//         }
//         _ => panic!("On line {}, unexpected word: {}", lineno, words[0]),
//     };
//     Line::Instr(instr)
// }
