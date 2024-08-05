use crate::vm::Instr;

pub(crate) fn assemble(s: &str) -> Vec<u8> {
    let mut instructions: Vec<Instr> = vec![];
    let mut ret: Vec<u8> = vec![];
    for (lineno, line) in s.lines().enumerate() {
        let words: Vec<_> = line.split_whitespace().collect();
        if words.is_empty() {
            continue;
        }
        instructions.push(assemble_instr(words, lineno));
    }
    for instr in instructions {
        instr.encode(&mut ret);
    }
    return ret;
}

fn assemble_instr(words: Vec<&str>, lineno: usize) -> Instr {
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
            let n = i64::from_str_radix(words[1], radix).unwrap();
            Instr::PushInt(n)
        }
        "jump" | "jumpif" | "call" => {
            let loc = usize::from_str_radix(words[1], radix).unwrap();
            match words[1] {
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
