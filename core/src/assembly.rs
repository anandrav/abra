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

pub type Instr = VmInstr<Label, String>;

impl From<&Instr> for String {
    fn from(val: &Instr) -> Self {
        match val {
            Instr::Pop => "pop".into(),
            Instr::Duplicate => "duplicate".into(),
            Instr::LoadOffset(n) => format!("load_offset {}", n),
            Instr::StoreOffset(n) => format!("store_offset {}", n),
            Instr::Add => "add".into(),
            Instr::Sub => "subtract".into(),
            Instr::Mul => "multiply".into(),
            Instr::Div => "divide".into(),
            Instr::Not => "not".into(),
            Instr::Equal => "equal".into(),
            Instr::LessThan => "less_than".into(),
            Instr::LessThanOrEqual => "less_than_or_equal".into(),
            Instr::GreaterThan => "greater_than".into(),
            Instr::GreaterThanOrEqual => "greater_than_or_equal".into(),
            Instr::PushNil => "push_nil".into(),
            Instr::PushBool(b) => format!("push_bool {}", b),
            Instr::PushInt(n) => format!("push_int {}", n),
            Instr::PushString(s) => format!("push_string \"{}\"", s),
            Instr::Jump(loc) => format!("jump {}", loc),
            Instr::JumpIf(loc) => format!("jump_if {}", loc),
            Instr::Call(loc) => format!("call {}", loc),
            Instr::CallFuncObj => "call_func_obj".into(),
            Instr::Return => "return".into(),
            Instr::Construct(n) => format!("construct {}", n),
            Instr::Deconstruct => "deconstruct".into(),
            Instr::GetField(idx) => format!("get_field {}", idx),
            Instr::SetField(idx) => format!("set_field {}", idx),
            Instr::GetIdx => "get_index".into(),
            Instr::SetIdx => "set_index".into(),
            Instr::ConstructVariant { tag } => format!("construct_variant {}", tag,),
            Instr::MakeClosure {
                n_captured,
                func_addr,
            } => format!("make_closure {} {}", n_captured, func_addr),
            Instr::Stop => "stop".into(),
            Instr::Effect(n) => format!("effect {}", n),
        }
    }
}

impl Display for Instr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let s: String = self.into();
        write!(f, "{}", s)
    }
}

pub(crate) fn assemble(s: &str) -> (Vec<VmInstr>, Vec<String>) {
    let mut instructions: Vec<InstrOrLabel> = vec![];
    let mut string_constants: HashMap<String, usize> = HashMap::new();
    for (lineno, line) in s.lines().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }
        instructions.push(assemble_instr_or_label(
            words,
            lineno,
            &mut string_constants,
        ));
    }
    let instructions = remove_labels(instructions, &string_constants);
    let mut string_table: Vec<String> = vec!["".into(); string_constants.len()];
    for (s, idx) in string_constants.iter() {
        string_table[*idx] = s.clone();
    }
    (instructions, string_table)
}

pub(crate) fn remove_labels(
    items: Vec<InstrOrLabel>,
    string_constants: &HashMap<String, usize>,
) -> Vec<VmInstr> {
    let mut ret: Vec<VmInstr> = vec![];
    let mut offset = 0;
    let mut label_to_idx: HashMap<Label, usize> = HashMap::new();
    for item in items.iter() {
        match item {
            InstrOrLabel::Instr(_) => {
                offset += 1;
            }
            InstrOrLabel::Label(label) => {
                label_to_idx.insert(label.clone(), offset);
            }
        }
    }

    for item in items {
        if let InstrOrLabel::Instr(instr) = item {
            ret.push(instr_to_vminstr(instr, &label_to_idx, string_constants));
        }
    }

    ret
}

fn get_label(s: &str) -> Option<String> {
    if s.ends_with(":") {
        Some(s[0..s.len() - 1].into())
    } else {
        None
    }
}

fn instr_to_vminstr(
    instr: Instr,
    label_to_idx: &HashMap<Label, usize>,
    string_constants: &HashMap<String, usize>,
) -> VmInstr {
    match instr {
        Instr::Pop => VmInstr::Pop,
        Instr::Duplicate => VmInstr::Duplicate,
        Instr::LoadOffset(i) => VmInstr::LoadOffset(i),
        Instr::StoreOffset(i) => VmInstr::StoreOffset(i),
        Instr::Add => VmInstr::Add,
        Instr::Sub => VmInstr::Sub,
        Instr::Mul => VmInstr::Mul,
        Instr::Div => VmInstr::Div,
        Instr::Not => VmInstr::Not,
        Instr::LessThan => VmInstr::LessThan,
        Instr::LessThanOrEqual => VmInstr::LessThanOrEqual,
        Instr::GreaterThan => VmInstr::GreaterThan,
        Instr::GreaterThanOrEqual => VmInstr::GreaterThanOrEqual,
        Instr::Equal => VmInstr::Equal,
        Instr::PushNil => VmInstr::PushNil,
        Instr::PushBool(b) => VmInstr::PushBool(b),
        Instr::PushInt(i) => VmInstr::PushInt(i),
        Instr::PushString(s) => VmInstr::PushString(string_constants[&s] as u16),
        Instr::Jump(label) => VmInstr::Jump(label_to_idx[&label]),
        Instr::JumpIf(label) => VmInstr::JumpIf(label_to_idx[&label]),
        Instr::Call(label) => VmInstr::Call(label_to_idx[&label]),
        Instr::CallFuncObj => VmInstr::CallFuncObj,
        Instr::Return => VmInstr::Return,
        Instr::Construct(n) => VmInstr::Construct(n),
        Instr::Deconstruct => VmInstr::Deconstruct,
        Instr::GetField(idx) => VmInstr::GetField(idx),
        Instr::SetField(idx) => VmInstr::SetField(idx),
        Instr::GetIdx => VmInstr::GetIdx,
        Instr::SetIdx => VmInstr::SetIdx,
        Instr::ConstructVariant { tag } => VmInstr::ConstructVariant { tag },
        Instr::MakeClosure {
            n_captured,
            func_addr,
        } => VmInstr::MakeClosure {
            n_captured,
            func_addr: label_to_idx[&func_addr],
        },
        Instr::Stop => VmInstr::Stop,
        Instr::Effect(n) => VmInstr::Effect(n),
    }
}

fn assemble_instr_or_label(
    words: Vec<&str>,
    lineno: usize,
    string_constants: &mut HashMap<String, usize>,
) -> InstrOrLabel {
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
        "subtract" => Instr::Sub,
        "multiply" => Instr::Mul,
        "divide" => Instr::Div,
        "not" => Instr::Not,
        "return" => Instr::Return,
        "stop" => Instr::Stop,
        "push_nil" => Instr::PushNil,
        "push_bool" => {
            let b = if words[1] == "true" {
                true
            } else if words[1] == "false" {
                false
            } else {
                panic!("On line {}, could not parse bool: {}", lineno, words[1]);
            };
            Instr::PushBool(b)
        }
        "push_int" => {
            let n = i64::from_str_radix(words[1], radix).unwrap();
            Instr::PushInt(n)
        }
        "push_string" => {
            // remove quotes
            let s = words[1][1..words[1].len() - 1].to_owned();
            let len = string_constants.len();
            string_constants.entry(s.clone()).or_insert(len);
            Instr::PushString(s)
        }
        "jump" | "jump_if" | "call" => {
            let loc = words[1].into();
            match words[0] {
                "jump" => Instr::Jump(loc),
                "jumpif" => Instr::JumpIf(loc),
                "call" => Instr::Call(loc),
                _ => unreachable!(),
            }
        }
        "construct" => {
            let n = u16::from_str_radix(words[1], radix).unwrap();
            Instr::Construct(n)
        }
        "deconstruct" => Instr::Deconstruct,
        "get_field" => {
            let n = u16::from_str_radix(words[1], radix).unwrap();
            Instr::GetField(n)
        }
        "set_field" => {
            let n = u16::from_str_radix(words[1], radix).unwrap();
            Instr::SetField(n)
        }
        "get_index" => Instr::GetIdx,
        "set_index" => Instr::SetIdx,
        "construct_variant" => {
            let tag = u16::from_str_radix(words[1], radix).unwrap();
            Instr::ConstructVariant { tag }
        }
        "effect" => {
            let n = u16::from_str_radix(words[1], radix).unwrap();
            Instr::Effect(n)
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
        let program_str = r#"push_int 3
push_int 4
subtract
push_int 5
add
"#;
        let (instructions, _) = assemble(program_str);
        let mut program_str2 = String::new();
        for instr in instructions {
            program_str2.push_str(&format!("{}\n", instr));
        }
        assert_eq!(program_str, program_str2);
    }
}
