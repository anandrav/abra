/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::translate_bytecode::{ConstantsHolder, LabelMap, Translator, TranslatorState};
use crate::vm::{AbraInt, CallData, Instr as VmInstr, ProgramCounter};
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
    StoreOffsetImm(i16, AbraInt),

    // Constants
    PushNil(u16),
    PushBool(bool),
    PushInt(AbraInt),
    PushFloat(String),
    PushString(String),

    // Arithmetic
    AddInt(Reg, Reg, Reg),
    AddIntImm(Reg, Reg, AbraInt),
    SubInt(Reg, Reg, Reg),
    SubIntImm(Reg, Reg, AbraInt),
    MulInt(Reg, Reg, Reg),
    MulIntImm(Reg, Reg, AbraInt),
    DivInt(Reg, Reg, Reg),
    DivIntImm(Reg, Reg, AbraInt),
    PowInt(Reg, Reg, Reg),
    PowIntImm(Reg, Reg, AbraInt),
    Modulo(Reg, Reg, Reg),
    ModuloImm(Reg, Reg, AbraInt),

    AddFloat(Reg, Reg, Reg),
    AddFloatImm(Reg, Reg, String),
    SubFloat(Reg, Reg, Reg),
    SubFloatImm(Reg, Reg, String),
    MulFloat(Reg, Reg, Reg),
    MulFloatImm(Reg, Reg, String),
    DivFloat(Reg, Reg, Reg),
    DivFloatImm(Reg, Reg, String),
    PowFloat(Reg, Reg, Reg),
    PowFloatImm(Reg, Reg, String),

    SquareRoot(Reg, Reg),

    // Logical
    Not,
    And,
    Or,

    // Comparison
    LessThanInt(Reg, Reg, Reg),
    LessThanIntImm(Reg, Reg, AbraInt),
    LessThanOrEqualInt(Reg, Reg, Reg),
    LessThanOrEqualIntImm(Reg, Reg, AbraInt),
    GreaterThanInt(Reg, Reg, Reg),
    GreaterThanIntImm(Reg, Reg, AbraInt),
    GreaterThanOrEqualInt(Reg, Reg, Reg),
    GreaterThanOrEqualIntImm(Reg, Reg, AbraInt),

    LessThanFloat(Reg, Reg, Reg),
    LessThanFloatImm(Reg, Reg, String),
    LessThanOrEqualFloat(Reg, Reg, Reg),
    LessThanOrEqualFloatImm(Reg, Reg, String),
    GreaterThanFloat(Reg, Reg, Reg),
    GreaterThanFloatImm(Reg, Reg, String),
    GreaterThanOrEqualFloat(Reg, Reg, Reg),
    GreaterThanOrEqualFloatImm(Reg, Reg, String),

    EqualInt(Reg, Reg, Reg),
    EqualIntImm(Reg, Reg, AbraInt),
    EqualFloat(Reg, Reg, Reg),
    EqualFloatImm(Reg, Reg, String),
    EqualBool(Reg, Reg, Reg),
    EqualString, // TODO: this is O(N). Must use smaller instructions. Or compare character-by-character and save progress in state of Vm

    // Control Flow
    Jump(Label),
    JumpIf(Label),
    JumpIfFalse(Label),
    Call(usize, Label),
    CallFuncObj(u32),
    CallExtern(u32),
    Return(u32),
    ReturnVoid,
    Stop, // used when returning from main function
    HostFunc(u16),
    Panic,

    // Data Structures
    ConstructStruct(u32),
    ConstructArray(u32),
    ConstructVariant { tag: u16 },
    DeconstructStruct,
    DeconstructVariant,
    GetField(u16, Reg),
    SetField(u16, Reg),
    GetIdx(Reg, Reg),
    SetIdx(Reg, Reg),
    MakeClosure { func_addr: Label },

    ArrayPush(Reg, Reg),
    ArrayPushIntImm(Reg, AbraInt),
    ArrayLength(Reg, Reg),
    ArrayPop(Reg, Reg),
    ConcatStrings, // TODO: this is O(N). Must use smaller instructions. Or concat character-by-character and save progress in Vm
    IntToFloat,
    FloatToInt,
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
                // We have 15 bits available to encode a stack offset
                const MAGNITUDE_BITS: u32 = 14;

                // Max:  16383
                const I15_MAX: i16 = (1 << MAGNITUDE_BITS) - 1;
                // Min: -16384
                const I15_MIN: i16 = -(1 << MAGNITUDE_BITS);

                if !(I15_MIN..=I15_MAX).contains(n) {
                    panic!(
                        "Jump offset {} out of 15-bit range ({} to {})",
                        n, I15_MIN, I15_MAX
                    );
                }

                (*n as u16) & 0b0111_1111_1111_1111
            }
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

// TODO: automate this please for crying out loud
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
            Instr::AddIntImm(dest, reg1, imm) => {
                write!(f, "add_int_imm {dest} {reg1} {imm}")
            }
            Instr::SubInt(dest, reg1, reg2) => {
                write!(f, "sub_int {dest} {reg1} {reg2}")
            }
            Instr::SubIntImm(dest, reg1, imm) => {
                write!(f, "sub_int_imm {dest} {reg1} {imm}")
            }
            Instr::MulInt(dest, reg1, reg2) => {
                write!(f, "multiply_int {dest} {reg1} {reg2}")
            }
            Instr::MulIntImm(dest, reg1, imm) => {
                write!(f, "mul_int_imm {dest} {reg1} {imm}")
            }
            Instr::DivInt(dest, reg1, reg2) => {
                write!(f, "divide_int {dest} {reg1} {reg2}")
            }
            Instr::DivIntImm(dest, reg1, imm) => {
                write!(f, "div_int_imm {dest} {reg1} {imm}")
            }
            Instr::PowInt(dest, reg1, reg2) => {
                write!(f, "power_int {dest} {reg1} {reg2}")
            }
            Instr::PowIntImm(dest, reg1, imm) => {
                write!(f, "power_int_imm {dest} {reg1} {imm}")
            }
            Instr::Modulo(dest, reg1, reg2) => {
                write!(f, "modulo {dest} {reg1} {reg2}")
            }
            Instr::ModuloImm(dest, reg1, imm) => {
                write!(f, "modulo_imm {dest} {reg1} {imm}")
            }
            Instr::AddFloat(dest, reg1, reg2) => {
                write!(f, "add_float {dest} {reg1} {reg2}")
            }
            Instr::AddFloatImm(dest, reg1, imm) => {
                write!(f, "add_float_imm {dest} {reg1} {imm}")
            }
            Instr::SubFloat(dest, reg1, reg2) => {
                write!(f, "sub_float {dest} {reg1} {reg2}")
            }
            Instr::SubFloatImm(dest, reg1, imm) => {
                write!(f, "sub_float_imm {dest} {reg1} {imm}")
            }
            Instr::MulFloat(dest, reg1, reg2) => {
                write!(f, "mul_float {dest} {reg1} {reg2}")
            }
            Instr::MulFloatImm(dest, reg1, imm) => {
                write!(f, "mul_float_imm {dest} {reg1} {imm}")
            }
            Instr::DivFloat(dest, reg1, reg2) => {
                write!(f, "div_float {dest} {reg1} {reg2}")
            }
            Instr::DivFloatImm(dest, reg1, imm) => {
                write!(f, "div_float_imm {dest} {reg1} {imm}")
            }
            Instr::PowFloat(dest, reg1, reg2) => {
                write!(f, "pow_float {dest} {reg1} {reg2}")
            }
            Instr::PowFloatImm(dest, reg1, imm) => {
                write!(f, "pow_float_imm {dest} {reg1} {imm}")
            }
            Instr::SquareRoot(dest, reg) => write!(f, "square_root {dest} {reg}"),
            Instr::Not => write!(f, "not"),
            Instr::And => write!(f, "and"),
            Instr::Or => write!(f, "or"),
            Instr::LessThanInt(dest, reg1, reg2) => {
                write!(f, "less_than_int {dest} {reg1} {reg2}")
            }
            Instr::LessThanIntImm(dest, reg1, imm) => {
                write!(f, "less_than_int_imm {dest} {reg1} {imm}")
            }
            Instr::LessThanOrEqualInt(dest, reg1, reg2) => {
                write!(f, "less_than_or_equal_int {dest} {reg1} {reg2}")
            }
            Instr::LessThanOrEqualIntImm(dest, reg1, imm) => {
                write!(f, "less_than_or_equal_int {dest} {reg1} {imm}")
            }
            Instr::GreaterThanInt(dest, reg1, reg2) => {
                write!(f, "greater_than_int {dest} {reg1} {reg2}")
            }
            Instr::GreaterThanIntImm(dest, reg1, imm) => {
                write!(f, "greater_than_int_imm {dest} {reg1} {imm}")
            }
            Instr::GreaterThanOrEqualInt(dest, reg1, reg2) => {
                write!(f, "greater_than_or_equal_int {dest} {reg1} {reg2}")
            }
            Instr::GreaterThanOrEqualIntImm(dest, reg1, imm) => {
                write!(f, "greater_than_or_equal_int_imm {dest} {reg1} {imm}")
            }
            Instr::LessThanFloat(dest, reg1, reg2) => {
                write!(f, "less_than_float {dest} {reg1} {reg2}")
            }
            Instr::LessThanFloatImm(dest, reg1, imm) => {
                write!(f, "less_than_float_imm {dest} {reg1} {imm}")
            }
            Instr::LessThanOrEqualFloat(dest, reg1, reg2) => {
                write!(f, "less_than_or_equal_float {dest} {reg1} {reg2}")
            }
            Instr::LessThanOrEqualFloatImm(dest, reg1, imm) => {
                write!(f, "less_than_or_equal_float_imm {dest} {reg1} {imm}")
            }
            Instr::GreaterThanFloat(dest, reg1, reg2) => {
                write!(f, "greater_than_float {dest} {reg1} {reg2}")
            }
            Instr::GreaterThanFloatImm(dest, reg1, imm) => {
                write!(f, "greater_than_float_imm {dest} {reg1} {imm}")
            }
            Instr::GreaterThanOrEqualFloat(dest, reg1, reg2) => {
                write!(f, "greater_than_or_equal_float {dest} {reg1} {reg2}")
            }
            Instr::GreaterThanOrEqualFloatImm(dest, reg1, imm) => {
                write!(f, "greater_than_or_equal_float_imm {dest} {reg1} {imm}")
            }
            Instr::EqualInt(dest, reg1, reg2) => write!(f, "equal_int {dest} {reg1} {reg2}"),
            Instr::EqualIntImm(dest, reg1, imm) => write!(f, "equal_int_imm {dest} {reg1} {imm}"),
            Instr::EqualFloat(dest, reg1, reg2) => write!(f, "equal_float {dest} {reg1} {reg2}"),
            Instr::EqualFloatImm(dest, reg1, imm) => {
                write!(f, "equal_float_imm {dest} {reg1} {imm}")
            }
            Instr::EqualBool(dest, reg1, reg2) => write!(f, "equal_bool {dest} {reg1} {reg2}"),
            Instr::EqualString => write!(f, "equal_string"),
            Instr::PushNil(n) => write!(f, "push_nil {n}"),
            Instr::PushBool(b) => write!(f, "push_bool {b}"),
            Instr::PushInt(n) => write!(f, "push_int {n}"),
            Instr::PushFloat(n) => write!(f, "push_float {n}"),
            Instr::PushString(s) => write!(f, "push_string {:?}", s),
            Instr::Jump(loc) => write!(f, "jump {loc}"),
            Instr::JumpIf(loc) => write!(f, "jump_if {loc}"),
            Instr::JumpIfFalse(loc) => write!(f, "jump_if_false {loc}"),
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
            Instr::GetField(index, offset) => write!(f, "get_field_offset {index} {offset}"),
            Instr::SetField(index, offset) => write!(f, "set_field_offset {index} {offset}"),
            Instr::GetIdx(reg1, reg2) => write!(f, "get_index_offset {reg1} {reg2}"),
            Instr::SetIdx(reg1, reg2) => write!(f, "set_index_offset {reg1} {reg2}"),
            Instr::MakeClosure { func_addr } => {
                write!(f, "make_closure {func_addr}")
            }
            Instr::ArrayPush(reg1, reg2) => write!(f, "array_push {reg1} {reg2}"),
            Instr::ArrayPushIntImm(reg1, imm) => write!(f, "array_push_int_imm {reg1} {imm}"),
            Instr::ArrayLength(dest, reg) => write!(f, "array_len {dest} {reg}"),
            Instr::ArrayPop(dest, reg) => write!(f, "array_pop {dest} {reg}"),
            Instr::ConcatStrings => write!(f, "concat_strings"),
            Instr::IntToFloat => write!(f, "int_to_float"),
            Instr::FloatToInt => write!(f, "float_to_int"),
            Instr::IntToString => write!(f, "int_to_string"),
            Instr::FloatToString => write!(f, "float_to_string"),
            Instr::HostFunc(n) => write!(f, "call_host {n}"),

            Instr::LoadLib => write!(f, "load_lib"),
            Instr::LoadForeignFunc => write!(f, "load_foreign_func"),
        }
    }
}

pub(crate) fn remove_labels_and_constants(
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
        Instr::StoreOffsetImm(i, imm) => {
            VmInstr::StoreOffsetImm(*i, constants.int_constants.try_get_id(imm).unwrap() as u16)
        }
        Instr::AddInt(dest, reg1, reg2) => {
            VmInstr::AddInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::AddIntImm(dest, reg1, imm) => VmInstr::AddIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::SubInt(dest, reg1, reg2) => {
            VmInstr::SubtractInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::SubIntImm(dest, reg1, imm) => VmInstr::SubIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::MulInt(dest, reg1, reg2) => {
            VmInstr::MulInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::MulIntImm(dest, reg1, imm) => VmInstr::MulIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::DivInt(dest, reg1, reg2) => {
            VmInstr::DivideInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::DivIntImm(dest, reg1, imm) => VmInstr::DivideIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::PowInt(dest, reg1, reg2) => {
            VmInstr::PowerInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::PowIntImm(dest, reg1, imm) => VmInstr::PowerIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::Modulo(dest, reg1, reg2) => {
            VmInstr::Modulo(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::ModuloImm(dest, reg1, imm) => VmInstr::ModuloImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::AddFloat(dest, reg1, reg2) => {
            VmInstr::AddFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::AddFloatImm(dest, reg1, imm) => VmInstr::AddFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::SubFloat(dest, reg1, reg2) => {
            VmInstr::SubFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::SubFloatImm(dest, reg1, imm) => VmInstr::SubFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::MulFloat(dest, reg1, reg2) => {
            VmInstr::MulFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::MulFloatImm(dest, reg1, imm) => VmInstr::MulFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::DivFloat(dest, reg1, reg2) => {
            VmInstr::DivFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::DivFloatImm(dest, reg1, imm) => VmInstr::DivFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::PowFloat(dest, reg1, reg2) => {
            VmInstr::PowerFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::PowFloatImm(dest, reg1, imm) => VmInstr::PowerFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::SquareRoot(dest, reg) => VmInstr::SquareRoot(dest.encode(), reg.encode()),
        Instr::Not => VmInstr::Not,
        Instr::And => VmInstr::And,
        Instr::Or => VmInstr::Or,
        Instr::LessThanInt(dest, reg1, reg2) => {
            VmInstr::LessThanInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::LessThanIntImm(dest, reg1, imm) => VmInstr::LessThanIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::LessThanOrEqualInt(dest, reg1, reg2) => {
            VmInstr::LessThanOrEqualInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::LessThanOrEqualIntImm(dest, reg1, imm) => VmInstr::LessThanOrEqualIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::GreaterThanInt(dest, reg1, reg2) => {
            VmInstr::GreaterThanInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::GreaterThanIntImm(dest, reg1, imm) => VmInstr::GreaterThanIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::GreaterThanOrEqualInt(dest, reg1, reg2) => {
            VmInstr::GreaterThanOrEqualInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::GreaterThanOrEqualIntImm(dest, reg1, imm) => VmInstr::GreaterThanOrEqualIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::LessThanFloat(dest, reg1, reg2) => {
            VmInstr::LessThanFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::LessThanFloatImm(dest, reg1, imm) => VmInstr::LessThanFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::LessThanOrEqualFloat(dest, reg1, reg2) => {
            VmInstr::LessThanOrEqualFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::LessThanOrEqualFloatImm(dest, reg1, imm) => VmInstr::LessThanOrEqualFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::GreaterThanFloat(dest, reg1, reg2) => {
            VmInstr::GreaterThanFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::GreaterThanFloatImm(dest, reg1, imm) => VmInstr::GreaterThanFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::GreaterThanOrEqualFloat(dest, reg1, reg2) => {
            VmInstr::GreaterThanOrEqualFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::GreaterThanOrEqualFloatImm(dest, reg1, imm) => VmInstr::GreaterThanOrEqualFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::EqualInt(dest, reg1, reg2) => {
            VmInstr::EqualInt(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::EqualIntImm(dest, reg1, imm) => VmInstr::EqualIntImm(
            dest.encode(),
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::EqualFloat(dest, reg1, reg2) => {
            VmInstr::EqualFloat(dest.encode(), reg1.encode(), reg2.encode())
        }
        Instr::EqualFloatImm(dest, reg1, imm) => VmInstr::EqualFloatImm(
            dest.encode(),
            reg1.encode(),
            constants.float_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::EqualBool(dest, reg1, reg2) => {
            VmInstr::EqualBool(dest.encode(), reg1.encode(), reg2.encode())
        }
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
        Instr::ConstructStruct(n) => VmInstr::ConstructStruct(*n),
        Instr::ConstructArray(n) => VmInstr::ConstructArray(*n),
        Instr::DeconstructStruct => VmInstr::DeconstructStruct,
        Instr::DeconstructVariant => VmInstr::DeconstructVariant,
        Instr::GetField(idx, offset) => VmInstr::GetFieldOffset(*idx, offset.encode()),
        Instr::SetField(idx, offset) => VmInstr::SetFieldOffset(*idx, offset.encode()),
        Instr::GetIdx(reg1, reg2) => VmInstr::GetIdxOffset(reg1.encode(), reg2.encode()),
        Instr::SetIdx(reg1, reg2) => VmInstr::SetIdxOffset(reg1.encode(), reg2.encode()),
        Instr::ConstructVariant { tag } => VmInstr::ConstructVariant { tag: *tag },
        Instr::MakeClosure { func_addr } => {
            // dbg!(func_addr);
            VmInstr::MakeClosure {
                func_addr: ProgramCounter::new(label_to_idx[func_addr]),
            }
        }
        Instr::ArrayPush(reg1, reg2) => VmInstr::ArrayPush(reg1.encode(), reg2.encode()),
        Instr::ArrayPushIntImm(reg1, imm) => VmInstr::ArrayPushIntImm(
            reg1.encode(),
            constants.int_constants.try_get_id(imm).unwrap() as u16,
        ),
        Instr::ArrayLength(dest, reg) => VmInstr::ArrayLength(dest.encode(), reg.encode()),
        Instr::ArrayPop(dest, reg) => VmInstr::ArrayPop(dest.encode(), reg.encode()),
        Instr::ConcatStrings => VmInstr::ConcatStrings,
        Instr::IntToFloat => VmInstr::IntToFloat,
        Instr::FloatToInt => VmInstr::FloatToInt,
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
//             let n = AbraInt::from_str_radix(words[1], radix).unwrap();
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
