use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
};

use crate::vm::Instr as VmInstr;

pub(crate) type Label = String;

#[derive(Debug)]
pub(crate) enum InstrOrLabel {
    Instr(Instr),
    Label(Label),
}

impl Display for InstrOrLabel {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            InstrOrLabel::Instr(instr) => write!(f, "{}", instr),
            InstrOrLabel::Label(label) => write!(f, "{}:", label),
        }
    }
}

#[derive(Debug)]
pub(crate) enum Instr {
    Pop,
    LoadOffset(i32),
    StoreOffset(i32),
    Add,
    Sub,
    Mul,
    Div,
    Return,
    Stop,
    PushNil,
    PushBool(bool),
    PushInt(i64),
    Jump(Label),
    JumpIf(Label),
    Call(Label, u8),
    MakeTuple(u8),
    UnpackTuple,
}

impl Into<String> for &Instr {
    fn into(self) -> String {
        match self {
            Instr::Pop => "pop".to_owned(),
            Instr::LoadOffset(n) => format!("loadoffset {}", n),
            Instr::StoreOffset(n) => format!("storeoffset {}", n),
            Instr::Add => "add".to_owned(),
            Instr::Sub => "sub".to_owned(),
            Instr::Mul => "mul".to_owned(),
            Instr::Div => "div".to_owned(),
            Instr::Return => "return".to_owned(),
            Instr::Stop => "stop".to_owned(),
            Instr::PushNil => "pushnil".to_owned(),
            Instr::PushBool(b) => format!("pushbool {}", b),
            Instr::PushInt(n) => format!("pushint {}", n),
            Instr::Jump(loc) => format!("jump {}", loc),
            Instr::JumpIf(loc) => format!("jumpif {}", loc),
            Instr::Call(loc, nargs) => format!("call {} {}", loc, nargs),
            Instr::MakeTuple(n) => format!("maketuple {}", n),
            Instr::UnpackTuple => "unpacktuple".to_owned(),
        }
    }
}

impl Display for Instr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let s: String = self.into();
        write!(f, "{}", s)
    }
}

pub(crate) fn assemble(s: &str) -> Vec<VmInstr> {
    let mut instructions: Vec<InstrOrLabel> = vec![];
    for (lineno, line) in s.lines().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }
        instructions.push(assemble_instr_or_label(words, lineno));
    }
    remove_labels(instructions)
}

pub(crate) fn remove_labels(items: Vec<InstrOrLabel>) -> Vec<VmInstr> {
    let mut ret: Vec<VmInstr> = vec![];
    let mut offset = 0;
    let mut label_to_idx: HashMap<Label, usize> = HashMap::new();
    for item in items.iter() {
        match item {
            InstrOrLabel::Instr(instr) => {
                offset += 1;
            }
            InstrOrLabel::Label(label) => {
                label_to_idx.insert(label.clone(), offset);
            }
        }
    }

    for item in items {
        if let InstrOrLabel::Instr(instr) = item {
            ret.push(instr_to_vminstr(instr, &label_to_idx));
        }
    }

    ret
}

fn get_label(s: &str) -> Option<String> {
    if s.ends_with(":") {
        Some(s[0..s.len() - 1].to_owned())
    } else {
        None
    }
}

fn instr_to_vminstr(instr: Instr, label_to_idx: &HashMap<Label, usize>) -> VmInstr {
    match instr {
        Instr::Pop => VmInstr::Pop,
        Instr::LoadOffset(i) => VmInstr::LoadOffset(i),
        Instr::StoreOffset(i) => VmInstr::StoreOffset(i),
        Instr::Add => VmInstr::Add,
        Instr::Sub => VmInstr::Sub,
        Instr::Mul => VmInstr::Mul,
        Instr::Div => VmInstr::Div,
        Instr::Return => VmInstr::Return,
        Instr::Stop => VmInstr::Stop,
        Instr::PushNil => VmInstr::PushNil,
        Instr::PushBool(b) => VmInstr::PushBool(b),
        Instr::PushInt(i) => VmInstr::PushInt(i),
        Instr::Jump(label) => VmInstr::Jump(label_to_idx[&label]),
        Instr::JumpIf(label) => VmInstr::JumpIf(label_to_idx[&label]),
        Instr::Call(label, nargs) => VmInstr::Call(label_to_idx[&label], nargs),
        Instr::MakeTuple(n) => VmInstr::MakeTuple(n),
        Instr::UnpackTuple => VmInstr::UnpackTuple,
    }
}

fn assemble_instr_or_label(words: Vec<&str>, lineno: usize) -> InstrOrLabel {
    if let Some(label) = get_label(words[0]) {
        return InstrOrLabel::Label(label);
    }
    let radix = 10;
    let instr = match words[0] {
        "pop" => Instr::Pop,
        "loadoffset" => {
            let n = i32::from_str_radix(words[1], radix).unwrap();
            Instr::LoadOffset(n)
        }
        "storeoffset" => {
            let n = i32::from_str_radix(words[1], radix).unwrap();
            Instr::StoreOffset(n)
        }
        "add" => Instr::Add,
        "sub" => Instr::Sub,
        "mul" => Instr::Mul,
        "div" => Instr::Div,
        "return" => Instr::Return,
        "stop" => Instr::Stop,
        "pushnil" => Instr::PushNil,
        "pushbool" => {
            let b = if words[1] == "true" {
                true
            } else if words[1] == "false" {
                false
            } else {
                panic!("On line {}, could not parse bool: {}", lineno, words[1]);
            };
            Instr::PushBool(b)
        }
        "pushint" => {
            let n = i64::from_str_radix(words[1], radix).unwrap();
            Instr::PushInt(n)
        }
        "jump" | "jumpif" | "call" => {
            let loc = words[1].to_owned();
            match words[0] {
                "jump" => Instr::Jump(loc),
                "jumpif" => Instr::JumpIf(loc),
                "call" => Instr::Call(loc, words[2].parse().unwrap()),
                _ => unreachable!(),
            }
        }
        _ => panic!("On line {}, unexpected word: {}", lineno, words[0]),
    };
    InstrOrLabel::Instr(instr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let program_str = r#"pushint 3
pushint 4
sub
pushint 5
add
"#;
        let instructions = assemble(program_str);
        let mut program_str2 = String::new();
        for instr in instructions {
            program_str2.push_str(&format!("{}\n", instr));
        }
        assert_eq!(program_str, program_str2);
    }
}
