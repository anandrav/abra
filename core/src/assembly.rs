use std::collections::HashMap;

use crate::ast::AbraInt;
use crate::vm::Instr;
use crate::vm::Opcode;

pub(crate) fn assemble(s: &str) -> Vec<u8> {
    let mut ret: Vec<u8> = vec![];
    let mut instructions: Vec<Instr> = vec![];
    let label_to_idx = build_map_label_to_idx(s);
    for (lineno, line) in s.lines().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }
        if get_label(words[0]).is_some() {
            continue;
        }
        instructions.push(assemble_instr(words, &label_to_idx, lineno));
    }
    for instr in instructions {
        instr.encode(&mut ret);
    }
    return ret;
}

fn build_map_label_to_idx(s: &str) -> HashMap<String, usize> {
    let mut ret: HashMap<String, usize> = HashMap::new();
    let mut offset = 0;
    for (lineno, line) in s.lines().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }
        let first = words[0];
        if let Some(label) = get_label(first) {
            ret.insert(label, offset);
        } else if let Some(opcode) = Opcode::from_str(first) {
            offset += opcode.nbytes();
        } else {
            panic!("On line {}, unexpected word: {}", lineno, first);
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

fn assemble_instr(words: Vec<&str>, label_to_idx: &HashMap<String, usize>, lineno: usize) -> Instr {
    let radix = 10;
    match words[0] {
        "pop" => Instr::Pop,
        "add" => Instr::Add,
        "sub" => Instr::Sub,
        "mul" => Instr::Mul,
        "div" => Instr::Div,
        "ret" => Instr::Return,
        "pushb" => {
            let b = if words[1] == "true" {
                true
            } else if words[1] == "false" {
                false
            } else {
                panic!("On line {}, could not parse bool: {}", lineno, words[1]);
            };
            Instr::PushBool(b)
        }
        "pushi" => {
            let n = AbraInt::from_str_radix(words[1], radix).unwrap();
            Instr::PushInt(n)
        }
        "jump" | "jumpif" | "call" => {
            let loc = *label_to_idx.get(words[1]).unwrap();
            match words[0] {
                "jump" => Instr::Jump(loc),
                "jumpif" => Instr::JumpIfTrue(loc),
                "call" => Instr::Call(loc),
                _ => unreachable!(),
            }
        }
        _ => panic!("On line {}, unexpected word: {}", lineno, words[0]),
    }
}

pub(crate) fn disassemble(program: &Vec<u8>) -> String {
    let mut ret = String::new();
    let mut pc = 0;
    while pc < program.len() {
        let instr = Instr::decode(&program[pc..]);
        pc += instr.size();
        let s: String = instr.into();
        ret.push_str(s.as_str());
        ret.push('\n');
    }
    ret
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic() {
        let program_str = r#"pushi 3
pushi 4
sub
pushi 5
add
"#;
        let program_bytes = assemble(program_str);
        let program_str2 = disassemble(&program_bytes);
        println!("{}", program_str2);
        assert_eq!(program_str, program_str2);
    }
}
