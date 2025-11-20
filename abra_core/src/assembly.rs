/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::translate_bytecode::{ConstantsHolder, LabelMap, Translator, TranslatorState};
use crate::vm::{CallData, Instr as VmInstr, ProgramCounter};
use std::fmt::{self, Display, Formatter};
use utils::hash::HashMap;

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

#[derive(Debug, Clone)]
pub enum Instr {
    // Stack manipulation
    Pop,
    Duplicate,
    LoadOffset(i16),
    StoreOffset(i16),
    StoreOffsetImm(i16, i16),

    // Constants
    PushNil(u16),
    PushBool(bool),
    PushInt(i64),
    PushFloat(String),
    PushString(String),

    // Arithmetic
    AddInt(Reg, Reg, Reg),
    IncrementRegImm(i16, i16),
    IncrementRegImmStk(i16, i16),
    SubtractInt,
    MulInt(Reg, Reg),
    DivideInt,
    PowerInt,
    Modulo,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    DivideFloat,
    PowerFloat,

    SquareRoot,

    // Logical
    Not,
    And,
    Or,

    // Comparison
    LessThanInt(Reg, Reg),
    LessThanOrEqualInt,
    GreaterThanInt,
    GreaterThanOrEqualInt,
    LessThanFloat,
    LessThanOrEqualFloat,
    GreaterThanFloat,
    GreaterThanOrEqualFloat,
    EqualInt,
    EqualFloat,
    EqualBool,
    EqualString, // TODO: this is O(N). Must use smaller instructions. Or compare character-by-character and save progress in state of Vm

    // Control Flow
    Jump(Label),
    JumpIf(Label),
    JumpIfFalse(Label),
    JumpIfLessThan(Label),
    Call(usize, Label),
    CallFuncObj(u32),
    CallExtern(u32),
    Return(u32),
    ReturnVoid,
    Stop, // used when returning from main function
    HostFunc(u16),
    Panic,

    // Data Structures
    ConstructStruct(usize),
    ConstructArray(usize),
    ConstructVariant { tag: u16 },
    DeconstructStruct,
    DeconstructVariant,
    GetField(u16),
    GetFieldOffset(u16, i16),
    SetField(u16),
    SetFieldOffset(u16, i16),
    GetIdx,
    GetIdxOffset(i16, i16),
    SetIdx,
    SetIdxOffset(i16, i16),
    MakeClosure { func_addr: Label },

    ArrayPush,
    ArrayLength,
    ArrayPop,
    ConcatStrings, // TODO: this is O(N). Must use smaller instructions. Or concat character-by-character and save progress in Vm
    IntToString,
    FloatToString,

    LoadLib,
    LoadForeignFunc,
}

#[derive(Debug, Clone)]
pub enum Reg {
    Offset(i16),
    Top,
}

impl Reg {
    pub(crate) fn encode(&self) -> u16 {
        match self {
            Reg::Top => {
                // high bit used to indicate stack top
                0b1000_0000_0000_0000
            }
            Reg::Offset(n) => {
                let n = *n as i16; // TODO: Offset should contain i16
                // We have 15 bits available to encode a stack offset
                const MAGNITUDE_BITS: u32 = 14;

                // Max:  16383
                const I15_MAX: i16 = (1 << MAGNITUDE_BITS) - 1;
                // Min: -16384
                const I15_MIN: i16 = -(1 << MAGNITUDE_BITS);

                if n > I15_MAX || n < I15_MIN {
                    panic!(
                        "Jump offset {} out of 15-bit range ({} to {})",
                        n, I15_MIN, I15_MAX
                    );
                }

                (n as u16) & 0b0111_1111_1111_1111
            }
        }
    }
}

// TODO: remove this soon
impl Reg {
    fn offset(&self) -> i16 {
        match self {
            Self::Offset(offs) => *offs,
            Self::Top => 0,
        }
    }
    fn use_stack(&self) -> u8 {
        match self {
            Self::Offset(_) => 0,
            Self::Top => 1,
        }
    }
}

impl Display for Reg {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            Reg::Offset(offs) => write!(f, "{}", offs),
            Reg::Top => write!(f, "top"),
        }
    }
}

impl Display for Instr {
    fn fmt(&self, f: &mut Formatter) -> core::fmt::Result {
        match self {
            Instr::Pop => write!(f, "pop"),
            Instr::Duplicate => write!(f, "duplicate"),
            Instr::LoadOffset(n) => write!(f, "load_offset {n}"),
            Instr::StoreOffset(n) => write!(f, "store_offset {n}"),
            Instr::StoreOffsetImm(n, imm) => write!(f, "store_offset_imm {n} {imm}"),
            Instr::AddInt(dest, reg1, reg2) => {
                write!(f, "add_int {dest} {reg1} {reg2}")
            }
            Instr::IncrementRegImm(reg, n) => write!(f, "incr_int_reg {reg} {n}"),
            Instr::IncrementRegImmStk(reg, n) => write!(f, "incr_int_reg_stk {reg} {n}"),
            Instr::SubtractInt => write!(f, "subtract_int"),
            Instr::MulInt(reg1, reg2) => {
                write!(f, "multiply_int {reg1} {reg2}")
            }
            Instr::DivideInt => write!(f, "divide_int"),
            Instr::PowerInt => write!(f, "power_int"),
            Instr::Modulo => write!(f, "modulo"),
            Instr::AddFloat => write!(f, "add_float"),
            Instr::SubtractFloat => write!(f, "subtract_float"),
            Instr::MultiplyFloat => write!(f, "multiply_float"),
            Instr::DivideFloat => write!(f, "divide_float"),
            Instr::PowerFloat => write!(f, "power_float"),
            Instr::SquareRoot => write!(f, "square_root"),
            Instr::Not => write!(f, "not"),
            Instr::And => write!(f, "and"),
            Instr::Or => write!(f, "or"),
            Instr::LessThanInt(reg1, reg2) => {
                write!(f, "less_than_int {reg1} {reg2}")
            }
            Instr::LessThanOrEqualInt => write!(f, "less_than_or_equal_int"),
            Instr::GreaterThanInt => write!(f, "greater_than_int"),
            Instr::GreaterThanOrEqualInt => write!(f, "greater_than_or_equal_int"),
            Instr::LessThanFloat => write!(f, "less_than_float"),
            Instr::LessThanOrEqualFloat => write!(f, "less_than_or_equal_float"),
            Instr::GreaterThanFloat => write!(f, "greater_than_float"),
            Instr::GreaterThanOrEqualFloat => write!(f, "greater_than_or_equal_float"),
            Instr::EqualInt => write!(f, "equal_int"),
            Instr::EqualFloat => write!(f, "equal_float"),
            Instr::EqualBool => write!(f, "equal_bool"),
            Instr::EqualString => write!(f, "equal_string"),
            Instr::PushNil(n) => write!(f, "push_nil {n}"),
            Instr::PushBool(b) => write!(f, "push_bool {b}"),
            Instr::PushInt(n) => write!(f, "push_int {n}"),
            Instr::PushFloat(n) => write!(f, "push_float {n}"),
            Instr::PushString(s) => write!(f, "push_string {:?}", s),
            Instr::Jump(loc) => write!(f, "jump {loc}"),
            Instr::JumpIf(loc) => write!(f, "jump_if {loc}"),
            Instr::JumpIfFalse(loc) => write!(f, "jump_if_false {loc}"),
            Instr::JumpIfLessThan(loc) => write!(f, "jump_if_less_than {loc}"),
            Instr::Call(nargs, addr) => {
                write!(f, "call {} {}", nargs, addr)
            }
            Instr::CallExtern(func_id) => write!(f, "call_extern {func_id}"),
            Instr::CallFuncObj(nargs) => write!(f, "call_func_obj {nargs}"),
            Instr::Return(nargs) => write!(f, "return {nargs}"),
            Instr::ReturnVoid => write!(f, "return"),
            Instr::Stop => write!(f, "stop"),
            Instr::Panic => write!(f, "panic"),
            Instr::ConstructStruct(n) => write!(f, "construct_struct {n}"),
            Instr::ConstructArray(n) => write!(f, "construct_array {n}"),
            Instr::ConstructVariant { tag } => {
                write!(f, "construct_variant {tag}")
            }
            Instr::DeconstructStruct => write!(f, "deconstruct_struct"),
            Instr::DeconstructVariant => write!(f, "deconstruct_variant"),
            Instr::GetField(n) => write!(f, "get_field {n}"),
            Instr::GetFieldOffset(index, offset) => write!(f, "get_field_offset {index} {offset}"),
            Instr::SetField(n) => write!(f, "set_field {n}"),
            Instr::SetFieldOffset(index, offset) => write!(f, "set_field_offset {index} {offset}"),
            Instr::GetIdx => write!(f, "get_index"),
            Instr::GetIdxOffset(reg1, reg2) => write!(f, "get_index_offset {reg1} {reg2}"),
            Instr::SetIdx => write!(f, "set_index"),
            Instr::SetIdxOffset(reg1, reg2) => write!(f, "set_index_offset {reg1} {reg2}"),
            Instr::MakeClosure { func_addr } => {
                write!(f, "make_closure {func_addr}")
            }
            Instr::ArrayPush => write!(f, "array_push"),
            Instr::ArrayLength => write!(f, "array_len"),
            Instr::ArrayPop => write!(f, "array_pop"),
            Instr::ConcatStrings => write!(f, "concat_strings"),
            Instr::IntToString => write!(f, "int_to_string"),
            Instr::FloatToString => write!(f, "float_to_string"),
            Instr::HostFunc(n) => write!(f, "call_host {n}"),

            Instr::LoadLib => write!(f, "load_lib"),
            Instr::LoadForeignFunc => write!(f, "load_foreign_func"),
        }
    }
}

pub(crate) fn remove_labels(
    items: &Vec<Line>,
    constants: &ConstantsHolder,
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
            instructions.push(instr_to_vminstr(instr, &label_to_idx, constants));
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
    constants: &ConstantsHolder,
) -> VmInstr {
    match instr {
        Instr::Pop => VmInstr::Pop,
        Instr::Duplicate => VmInstr::Duplicate,
        Instr::LoadOffset(i) => VmInstr::LoadOffset(*i),
        Instr::StoreOffset(i) => VmInstr::StoreOffset(*i),
        Instr::StoreOffsetImm(i, imm) => VmInstr::StoreOffsetImm(*i, *imm),
        Instr::AddInt(dest, reg1, reg2) => {
            VmInstr::AddInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::IncrementRegImm(reg, n) => VmInstr::IncrementRegImm(*reg, *n),
        Instr::IncrementRegImmStk(reg, n) => VmInstr::IncrementRegImmStk(*reg, *n),
        Instr::SubtractInt => VmInstr::SubtractInt,
        Instr::MulInt(reg1, reg2) => VmInstr::MulInt(
            reg1.offset(),
            reg1.use_stack(),
            reg2.offset(),
            reg2.use_stack(),
        ),
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
        Instr::LessThanInt(reg1, reg2) => VmInstr::LessThanInt(
            reg1.offset(),
            reg1.use_stack(),
            reg2.offset(),
            reg2.use_stack(),
        ),
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
        Instr::PushInt(i) => VmInstr::PushInt(constants.int_constants.try_get_id(i).unwrap()),
        Instr::PushFloat(f) => VmInstr::PushFloat(constants.float_constants.try_get_id(f).unwrap()),
        Instr::PushString(s) => {
            VmInstr::PushString(constants.string_constants.try_get_id(s).unwrap())
        }
        Instr::Jump(label) => VmInstr::Jump(ProgramCounter::new(label_to_idx[label])),
        Instr::JumpIf(label) => VmInstr::JumpIf(ProgramCounter::new(label_to_idx[label])),
        Instr::JumpIfFalse(label) => VmInstr::JumpIfFalse(ProgramCounter::new(label_to_idx[label])),
        Instr::JumpIfLessThan(label) => {
            VmInstr::JumpIfLessThan(ProgramCounter::new(label_to_idx[label]))
        }
        Instr::Call(nargs, label) => VmInstr::Call(CallData::new(
            *nargs as u32,
            *label_to_idx
                .get(label)
                .unwrap_or_else(|| panic!("Could not find label: {label}")) as u32,
        )),
        Instr::CallExtern(func_id) => VmInstr::CallExtern(*func_id),
        Instr::CallFuncObj(nargs) => VmInstr::CallFuncObj(*nargs),
        Instr::Return(nargs) => VmInstr::Return(*nargs),
        Instr::ReturnVoid => VmInstr::ReturnVoid,
        Instr::Stop => VmInstr::Stop,
        Instr::Panic => VmInstr::Panic,
        Instr::ConstructStruct(n) => VmInstr::ConstructStruct(*n as u32),
        Instr::ConstructArray(n) => VmInstr::ConstructArray(*n as u32),
        Instr::DeconstructStruct => VmInstr::DeconstructStruct,
        Instr::DeconstructVariant => VmInstr::DeconstructVariant,
        Instr::GetField(idx) => VmInstr::GetField(*idx),
        Instr::GetFieldOffset(idx, offset) => VmInstr::GetFieldOffset(*idx, *offset),
        Instr::SetField(idx) => VmInstr::SetField(*idx),
        Instr::SetFieldOffset(idx, offset) => VmInstr::SetFieldOffset(*idx, *offset),
        Instr::GetIdx => VmInstr::GetIdx,
        Instr::GetIdxOffset(reg1, reg2) => VmInstr::GetIdxOffset(*reg1, *reg2),
        Instr::SetIdx => VmInstr::SetIdx,
        Instr::SetIdxOffset(reg1, reg2) => VmInstr::SetIdxOffset(*reg1, *reg2),
        Instr::ConstructVariant { tag } => VmInstr::ConstructVariant { tag: *tag },
        Instr::MakeClosure { func_addr } => {
            // dbg!(func_addr);
            VmInstr::MakeClosure {
                func_addr: ProgramCounter::new(label_to_idx[func_addr]),
            }
        }
        Instr::ArrayPush => VmInstr::ArrayPush,
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
