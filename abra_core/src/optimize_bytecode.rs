/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::assembly::{Instr, Line, Reg};

pub(crate) fn optimize(lines: Vec<Line>) -> Vec<Line> {
    let mut len = lines.len();
    let mut ret = lines;
    loop {
        ret = optimization_pass(ret);
        if ret.len() < len {
            len = ret.len();
        } else {
            break;
        }
    }
    ret
}

fn optimization_pass(lines: Vec<Line>) -> Vec<Line> {
    let mut ret: Vec<Line> = Vec::with_capacity(lines.len());

    let mut index = 0;
    while index < lines.len() {
        let curr = &lines[index];

        if peephole3_helper(&lines, &mut index, &mut ret) {
            continue;
        }
        if peephole2_helper(&lines, &mut index, &mut ret) {
            continue;
        }
        if peephole1_helper(&lines, &mut index, &mut ret) {
            continue;
        }

        ret.push(curr.clone());
        index += 1;
    }

    ret
}

fn peephole1_helper(lines: &[Line], index: &mut usize, _ret: &mut Vec<Line>) -> bool {
    match lines[*index].clone() {
        Line::Label(_) => false,
        Line::Instr {
            instr: instr1,
            lineno: _,
            file_id: _,
            func_id: _,
        } => {
            match instr1 {
                // PUSH 0 -> nothing
                Instr::PushNil(0) => {
                    *index += 1;
                    true
                }
                _ => false,
            }
        }
    }
}

fn peephole2_helper(lines: &[Line], index: &mut usize, ret: &mut Vec<Line>) -> bool {
    match lines[*index].clone() {
        Line::Label(_) => false,
        Line::Instr {
            instr: instr1,
            lineno,
            file_id,
            func_id,
        } => {
            if *index + 1 < lines.len()
                && let Line::Instr { instr: instr2, .. } = &lines[*index + 1]
            {
                match (instr1, instr2) {
                    // PUSH POP
                    (Instr::PushNil(n), Instr::Pop) => {
                        ret.push(Line::Instr {
                            instr: Instr::PushNil(n - 1),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    (
                        Instr::PushBool(_)
                        | Instr::PushFloat(_)
                        | Instr::PushInt(_)
                        | Instr::PushString(_),
                        Instr::Pop,
                    ) => {
                        *index += 2;
                        true
                    }
                    (Instr::Duplicate, Instr::Pop) => {
                        *index += 2;
                        true
                    }
                    // NOT JUMP_IF -> JUMP_IF_FALSE
                    (Instr::Not, Instr::JumpIf(label)) => {
                        ret.push(Line::Instr {
                            instr: Instr::JumpIfFalse(label.clone()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // PUSH TRUE JUMP IF
                    (Instr::PushBool(true), Instr::JumpIf(label)) => {
                        ret.push(Line::Instr {
                            instr: Instr::Jump(label.clone()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // BOOLEAN FLIP
                    (Instr::PushBool(b), Instr::Not) => {
                        ret.push(Line::Instr {
                            instr: Instr::PushBool(!b),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // // LOADOFFSET GETFIELD
                    (Instr::LoadOffset(offset), Instr::GetField(field)) => {
                        ret.push(Line::Instr {
                            instr: Instr::GetFieldOffset(*field, offset),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // LOADOFFSET SETFIELD
                    (Instr::LoadOffset(offset), Instr::SetField(field)) => {
                        ret.push(Line::Instr {
                            instr: Instr::SetFieldOffset(*field, offset),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // PUSHINT STORE -> STORE IMM
                    (Instr::PushInt(n), Instr::StoreOffset(offset)) if fits_imm(n) => {
                        ret.push(Line::Instr {
                            instr: Instr::StoreOffsetImm(*offset, as_imm(n)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // LOAD(X) <ANY>(_, _, TOP) -> __(_, _, X)
                    (Instr::LoadOffset(offset), instr2) if instr2.second_arg_is_top() => {
                        ret.push(Line::Instr {
                            instr: instr2.clone().replace_second_arg(Reg::Offset(offset)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // LOAD(X) __(_, TOP, Offset(Y) | Imm) -> __(_, X, Offset(Y) | Imm)
                    (Instr::LoadOffset(offset), instr2)
                        if instr2.first_arg_is_top_and_second_arg_is_offset_or_imm() =>
                    {
                        ret.push(Line::Instr {
                            instr: instr2.clone().replace_first_arg(Reg::Offset(offset)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // __(TOP, R1, R2) STORE(N) -> __(N, R1, R2)
                    (instr1, Instr::StoreOffset(offset)) if instr1.dest_is_top() => {
                        ret.push(Line::Instr {
                            instr: instr1.replace_dest(Reg::Offset(*offset)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2;
                        true
                    }
                    // PUSHINT(N) ADD_INT(_, _, TOP) -> ADD_INT_IMM(_, _, N)
                    (instr1, instr2)
                        if instr1.is_push_imm()
                            && instr2.second_arg_is_top()
                            && instr2.can_replace_second_arg_with_imm() =>
                    {
                        ret.push(Line::Instr {
                            instr: instr2.clone().replace_second_arg_imm(instr1.get_imm()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2; // TODO: doing + 2 everywhere is redundant and error prone. fix here and in other peephole functions
                        true
                    }
                    _ => false,
                }
            } else {
                false
            }
        }
    }
}

fn peephole3_helper(lines: &[Line], index: &mut usize, ret: &mut Vec<Line>) -> bool {
    match lines[*index].clone() {
        Line::Label(_) => false,
        Line::Instr {
            instr: instr1,
            lineno,
            file_id,
            func_id,
        } => {
            // WINDOW SIZE 3
            if *index + 2 < lines.len()
                && let Line::Instr { instr: instr2, .. } = &lines[*index + 1]
                && let Line::Instr { instr: instr3, .. } = &lines[*index + 2]
            {
                match (instr1, instr2, instr3) {
                    // LOAD LOAD GET_INDEX
                    (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::GetIdx) => {
                        ret.push(Line::Instr {
                            instr: Instr::GetIdxOffset(reg1, *reg2),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // LOAD LOAD SET_INDEX
                    (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::SetIdx) => {
                        ret.push(Line::Instr {
                            instr: Instr::SetIdxOffset(reg1, *reg2),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD INT ADDITION
                    (
                        Instr::PushInt(a),
                        Instr::PushInt(b),
                        Instr::AddInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
                        let c = a.wrapping_add(*b); // TODO: checked_add here and everywhere else
                        ret.push(Line::Instr {
                            instr: Instr::PushInt(c),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD INT SUBTRACTION
                    (
                        Instr::PushInt(a),
                        Instr::PushInt(b),
                        Instr::SubInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
                        let c = a.wrapping_sub(*b);
                        ret.push(Line::Instr {
                            instr: Instr::PushInt(c),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD INT MULTIPLICATION
                    (
                        Instr::PushInt(a),
                        Instr::PushInt(b),
                        Instr::MulInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
                        let c = a.wrapping_mul(*b);
                        ret.push(Line::Instr {
                            instr: Instr::PushInt(c),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD INT DIVISION
                    (Instr::PushInt(a), Instr::PushInt(b), Instr::DivideInt) => {
                        if *b == 0 {
                            false
                        } else {
                            let c = a.wrapping_div(*b);
                            ret.push(Line::Instr {
                                instr: Instr::PushInt(c),
                                lineno,
                                file_id,
                                func_id,
                            });
                            *index += 3;
                            true
                        }
                    }
                    // FOLD INT EXPONENTIATION
                    (Instr::PushInt(a), Instr::PushInt(b), Instr::PowerInt) => {
                        let c = a.wrapping_pow(*b as u32);
                        ret.push(Line::Instr {
                            instr: Instr::PushInt(c),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD FLOAT ADDITION
                    (Instr::PushFloat(a), Instr::PushFloat(b), Instr::AddFloat) => {
                        let a = a.parse::<f64>().unwrap();
                        let b = b.parse::<f64>().unwrap();
                        let c = a + b;
                        ret.push(Line::Instr {
                            instr: Instr::PushFloat(c.to_string()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD FLOAT SUBTRACTION
                    (Instr::PushFloat(a), Instr::PushFloat(b), Instr::SubtractFloat) => {
                        let a = a.parse::<f64>().unwrap();
                        let b = b.parse::<f64>().unwrap();
                        let c = a - b;
                        ret.push(Line::Instr {
                            instr: Instr::PushFloat(c.to_string()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD FLOAT MULTIPLICATION
                    (Instr::PushFloat(a), Instr::PushFloat(b), Instr::MultiplyFloat) => {
                        let a = a.parse::<f64>().unwrap();
                        let b = b.parse::<f64>().unwrap();
                        let c = a * b;
                        ret.push(Line::Instr {
                            instr: Instr::PushFloat(c.to_string()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD FLOAT DIVISION
                    (Instr::PushFloat(a), Instr::PushFloat(b), Instr::DivideFloat) => {
                        let a = a.parse::<f64>().unwrap();
                        let b = b.parse::<f64>().unwrap();
                        let c = a / b;
                        ret.push(Line::Instr {
                            instr: Instr::PushFloat(c.to_string()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // FOLD FLOAT EXPONENTIATION
                    (Instr::PushFloat(a), Instr::PushFloat(b), Instr::PowerFloat) => {
                        let a = a.parse::<f64>().unwrap();
                        let b = b.parse::<f64>().unwrap();
                        let c = a.powf(b);
                        ret.push(Line::Instr {
                            instr: Instr::PushFloat(c.to_string()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    _ => false,
                }
            } else {
                false
            }
        }
    }
}

fn fits_imm(n: i64) -> bool {
    let n: Result<i16, _> = n.try_into();
    n.is_ok()
}

fn as_imm(n: i64) -> i16 {
    n.try_into().unwrap()
}

// fn as_imm_bool(b: bool) -> i16 {
//     if b { 1 } else { 0 }
// }

impl Instr {
    fn second_arg_is_top(&self) -> bool {
        match self {
            Instr::AddInt(_, _, Reg::Top) => true,
            Instr::SubInt(_, _, Reg::Top) => true,
            Instr::MulInt(_, _, Reg::Top) => true,
            Instr::LessThanInt(_, _, Reg::Top) => true,
            Instr::EqualInt(_, _, Reg::Top) => true,
            Instr::ArrayPush(_, Reg::Top) => true,
            _ => false,
        }
    }
    fn first_arg_is_top_and_second_arg_is_offset_or_imm(&self) -> bool {
        match self {
            Instr::AddInt(_, Reg::Top, Reg::Offset(_)) => true,
            Instr::AddIntImm(_, Reg::Top, _) => true,
            Instr::SubInt(_, Reg::Top, Reg::Offset(_)) => true,
            Instr::SubIntImm(_, Reg::Top, _) => true,
            Instr::MulInt(_, Reg::Top, Reg::Offset(_)) => true,
            Instr::LessThanInt(_, Reg::Top, Reg::Offset(_)) => true,
            Instr::LessThanIntImm(_, Reg::Top, _) => true,
            Instr::EqualInt(_, Reg::Top, Reg::Offset(_)) => true,
            Instr::EqualIntImm(_, Reg::Top, _) => true,
            Instr::ArrayPush(Reg::Top, Reg::Offset(_)) => true,
            Instr::ArrayPushImm(Reg::Top, _) => true,
            _ => false,
        }
    }

    fn dest_is_top(&self) -> bool {
        match self {
            Instr::AddInt(Reg::Top, _, _) => true,
            Instr::AddIntImm(Reg::Top, _, _) => true,
            Instr::SubInt(Reg::Top, _, _) => true,
            Instr::SubIntImm(Reg::Top, _, _) => true,
            Instr::MulInt(Reg::Top, _, _) => true,
            Instr::LessThanInt(Reg::Top, _, _) => true,
            Instr::LessThanIntImm(Reg::Top, _, _) => true,
            Instr::EqualInt(Reg::Top, _, _) => true,
            Instr::EqualIntImm(Reg::Top, _, _) => true,
            _ => false,
        }
    }

    fn replace_first_arg(self, r1: Reg) -> Instr {
        match self {
            Instr::AddInt(dest, _, r2) => Instr::AddInt(dest, r1, r2),
            Instr::AddIntImm(dest, _, r2) => Instr::AddIntImm(dest, r1, r2),
            Instr::SubInt(dest, _, r2) => Instr::SubInt(dest, r1, r2),
            Instr::SubIntImm(dest, _, r2) => Instr::SubIntImm(dest, r1, r2),
            Instr::MulInt(dest, _, r2) => Instr::MulInt(dest, r1, r2),
            Instr::LessThanInt(dest, _, r2) => Instr::LessThanInt(dest, r1, r2),
            Instr::LessThanIntImm(dest, _, r2) => Instr::LessThanIntImm(dest, r1, r2),
            Instr::EqualInt(dest, _, r2) => Instr::EqualInt(dest, r1, r2),
            Instr::EqualIntImm(dest, _, r2) => Instr::EqualIntImm(dest, r1, r2),
            Instr::ArrayPush(_, r2) => Instr::ArrayPush(r1, r2),
            Instr::ArrayPushImm(_, r2) => Instr::ArrayPushImm(r1, r2),
            _ => panic!("can't replace first arg"),
        }
    }

    fn replace_second_arg(self, r2: Reg) -> Instr {
        match self {
            Instr::AddInt(dest, r1, _) => Instr::AddInt(dest, r1, r2),
            Instr::MulInt(dest, r1, _) => Instr::MulInt(dest, r1, r2),
            Instr::SubInt(dest, r1, _) => Instr::SubInt(dest, r1, r2),
            Instr::LessThanInt(dest, r1, _) => Instr::LessThanInt(dest, r1, r2),
            Instr::EqualInt(dest, r1, _) => Instr::EqualInt(dest, r1, r2),
            Instr::ArrayPush(r1, _) => Instr::ArrayPush(r1, r2),
            _ => panic!("can't replace second arg"),
        }
    }

    fn replace_dest(self, dest: Reg) -> Instr {
        match self {
            Instr::AddInt(_, r1, r2) => Instr::AddInt(dest, r1, r2),
            Instr::AddIntImm(_, r1, r2) => Instr::AddIntImm(dest, r1, r2),
            Instr::SubInt(_, r1, r2) => Instr::SubInt(dest, r1, r2),
            Instr::SubIntImm(_, r1, r2) => Instr::SubIntImm(dest, r1, r2),
            Instr::MulInt(_, r1, r2) => Instr::MulInt(dest, r1, r2),
            Instr::LessThanInt(_, r1, r2) => Instr::LessThanInt(dest, r1, r2),
            Instr::LessThanIntImm(_, r1, r2) => Instr::LessThanIntImm(dest, r1, r2),
            Instr::EqualInt(_, r1, r2) => Instr::EqualInt(dest, r1, r2),
            Instr::EqualIntImm(_, r1, r2) => Instr::EqualIntImm(dest, r1, r2),
            _ => panic!("can't replace dest"),
        }
    }

    fn is_push_imm(&self) -> bool {
        match self {
            Instr::PushInt(n) => fits_imm(*n),
            // Instr::PushBool(_) => true,
            _ => false,
        }
    }

    fn get_imm(&self) -> i16 {
        match self {
            Instr::PushInt(n) => as_imm(*n),
            // Instr::PushBool(b) => as_imm_bool(*b), // boolean immediates are represented as int immediates
            _ => panic!("can't get immediate"),
        }
    }

    fn can_replace_second_arg_with_imm(&self) -> bool {
        match self {
            Instr::AddInt(..) => true,
            Instr::SubInt(..) => true,
            Instr::LessThanInt(..) => true,
            Instr::EqualInt(..) => true,
            Instr::ArrayPush(..) => true,
            _ => false,
        }
    }

    fn replace_second_arg_imm(self, imm: i16) -> Instr {
        match self {
            Instr::AddInt(dest, r1, _) => Instr::AddIntImm(dest, r1, imm),
            Instr::SubInt(dest, r1, _) => Instr::SubIntImm(dest, r1, imm),
            Instr::LessThanInt(dest, r1, _) => Instr::LessThanIntImm(dest, r1, imm),
            Instr::EqualInt(dest, r1, _) => Instr::EqualIntImm(dest, r1, imm),
            Instr::ArrayPush(r1, _) => Instr::ArrayPushImm(r1, imm),
            _ => panic!("can't replace second arg with immediate"),
        }
    }
}
