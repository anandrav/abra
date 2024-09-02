use std::{
    collections::HashMap,
    fmt::{self, Display, Formatter},
};

use crate::{translate_bytecode::CompiledProgram, vm::Instr as VmInstr};

pub(crate) type Label = String;

use crate::translate_bytecode::LabelMap;

#[derive(Debug)]
pub(crate) enum Item {
    Instr(Instr),
    Label(Label),
}

impl From<Instr> for Item {
    fn from(instr: Instr) -> Self {
        Item::Instr(instr)
    }
}

impl From<Label> for Item {
    fn from(label: Label) -> Self {
        Item::Label(label)
    }
}

impl Display for Item {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Item::Instr(instr) => write!(f, "{}", instr),
            Item::Label(label) => write!(f, "{}:", label),
        }
    }
}

pub type Instr = VmInstr<Label, String>;

pub(crate) fn _assemble(s: &str) -> CompiledProgram {
    let mut instructions: Vec<Item> = vec![];
    let mut string_constants: HashMap<String, usize> = HashMap::new();
    for (lineno, line) in s.lines().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }
        instructions.push(_assemble_instr_or_label(
            words,
            lineno,
            &mut string_constants,
        ));
    }
    let (instructions, label_map) = remove_labels(&instructions, &string_constants);
    let mut string_table: Vec<String> = vec!["".into(); string_constants.len()];
    for (s, idx) in string_constants.iter() {
        string_table[*idx] = s.clone();
    }
    CompiledProgram {
        instructions,
        label_map,
        string_table,
    }
}

pub(crate) fn remove_labels(
    items: &Vec<Item>,
    string_constants: &HashMap<String, usize>,
) -> (Vec<VmInstr>, LabelMap) {
    let mut instructions: Vec<VmInstr> = vec![];
    let mut offset = 0;
    let mut label_to_idx: LabelMap = HashMap::new();
    for item in items.iter() {
        match item {
            Item::Instr(_) => {
                offset += 1;
            }
            Item::Label(label) => {
                label_to_idx.insert(label.clone(), offset);
            }
        }
    }

    for item in items {
        if let Item::Instr(instr) = item {
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
    string_constants: &HashMap<String, usize>,
) -> VmInstr {
    match instr {
        Instr::Pop => VmInstr::Pop,
        Instr::Duplicate => VmInstr::Duplicate,
        Instr::LoadOffset(i) => VmInstr::LoadOffset(*i),
        Instr::StoreOffset(i) => VmInstr::StoreOffset(*i),
        Instr::Add => VmInstr::Add,
        Instr::Subtract => VmInstr::Subtract,
        Instr::Multiply => VmInstr::Multiply,
        Instr::Divide => VmInstr::Divide,
        Instr::SquareRoot => VmInstr::SquareRoot,
        Instr::Power => VmInstr::Power,
        Instr::Not => VmInstr::Not,
        Instr::And => VmInstr::And,
        Instr::Or => VmInstr::Or,
        Instr::LessThan => VmInstr::LessThan,
        Instr::LessThanOrEqual => VmInstr::LessThanOrEqual,
        Instr::GreaterThan => VmInstr::GreaterThan,
        Instr::GreaterThanOrEqual => VmInstr::GreaterThanOrEqual,
        Instr::Equal => VmInstr::Equal,
        Instr::PushNil => VmInstr::PushNil,
        Instr::PushBool(b) => VmInstr::PushBool(*b),
        Instr::PushInt(i) => VmInstr::PushInt(*i),
        Instr::PushFloat(f) => VmInstr::PushFloat(*f),
        Instr::PushString(s) => VmInstr::PushString(string_constants[s] as u16),
        Instr::Jump(label) => VmInstr::Jump(label_to_idx[label]),
        Instr::JumpIf(label) => VmInstr::JumpIf(label_to_idx[label]),
        Instr::Call(label) => VmInstr::Call(
            *label_to_idx
                .get(label)
                .unwrap_or_else(|| panic!("Could not find label: {}", label)),
        ),
        Instr::CallFuncObj => VmInstr::CallFuncObj,
        Instr::Return => VmInstr::Return,
        Instr::Construct(n) => VmInstr::Construct(*n),
        Instr::Deconstruct => VmInstr::Deconstruct,
        Instr::GetField(idx) => VmInstr::GetField(*idx),
        Instr::SetField(idx) => VmInstr::SetField(*idx),
        Instr::GetIdx => VmInstr::GetIdx,
        Instr::SetIdx => VmInstr::SetIdx,
        Instr::ConstructVariant { tag } => VmInstr::ConstructVariant { tag: *tag },
        Instr::MakeClosure {
            n_captured,
            func_addr,
        } => VmInstr::MakeClosure {
            n_captured: *n_captured,
            func_addr: label_to_idx[func_addr],
        },
        Instr::ArrayAppend => VmInstr::ArrayAppend,
        Instr::ArrayLen => VmInstr::ArrayLen,
        Instr::ArrayPop => VmInstr::ArrayPop,
        Instr::ConcatStrings => VmInstr::ConcatStrings,
        Instr::IntToString => VmInstr::IntToString,
        Instr::FloatToString => VmInstr::FloatToString,
        Instr::Effect(n) => VmInstr::Effect(*n),
    }
}

fn _assemble_instr_or_label(
    words: Vec<&str>,
    lineno: usize,
    string_constants: &mut HashMap<String, usize>,
) -> Item {
    if let Some(label) = _get_label(words[0]) {
        return Item::Label(label);
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
        "subtract" => Instr::Subtract,
        "multiply" => Instr::Multiply,
        "divide" => Instr::Divide,
        "not" => Instr::Not,
        "return" => Instr::Return,
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
    Item::Instr(instr)
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
        let program = _assemble(program_str);
        let instructions = program.instructions;
        let mut program_str2 = String::new();
        for instr in instructions {
            program_str2.push_str(&format!("{}\n", instr));
        }
        assert_eq!(program_str, program_str2);
    }
}
