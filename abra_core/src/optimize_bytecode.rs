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

        if peephole4_helper(&lines, &mut index, &mut ret) {
            continue;
        }
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
                    // TODO: is this optimization worth it? Will it prevent other less than optimizations?
                    // LESS_THAN_INT JUMPIF -> JUMP_IF_LESS_THAN
                    (Instr::LessThanInt(Reg::Top, Reg::Top, Reg::Top), Instr::JumpIf(label)) => {
                        ret.push(Line::Instr {
                            instr: Instr::JumpIfLessThan(label.clone()),
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
                    // LOAD(X) __(_, TOP, Offset(Y)) -> __(_, X, Offset(Y))
                    (Instr::LoadOffset(offset), instr2)
                        if instr2.first_arg_is_top_and_second_arg_is_offset() =>
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
                    // LOAD(X) PUSH(n) ADD_INT STORE(X) -> INCR_STK(X)
                    (
                        Instr::LoadOffset(reg1),
                        Instr::PushInt(n),
                        Instr::AddInt(Reg::Top, Reg::Top, Reg::Top),
                    ) if fits_imm(*n) => {
                        ret.push(Line::Instr {
                            instr: Instr::IncrementRegImmStk(reg1, as_imm(*n)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // LOAD(X) PUSH(n) SUB_INT STORE(X) -> INCR_STK(X)
                    (Instr::LoadOffset(reg1), Instr::PushInt(n), Instr::SubtractInt)
                        if fits_imm(-n) =>
                    {
                        ret.push(Line::Instr {
                            instr: Instr::IncrementRegImmStk(reg1, as_imm(-n)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // LOAD LOAD MUL_INT
                    (
                        Instr::LoadOffset(reg1),
                        Instr::LoadOffset(reg2),
                        // TODO: change this to work for any dest, not just top. same for other instructions
                        Instr::MulInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
                        ret.push(Line::Instr {
                            instr: Instr::MulInt(Reg::Top, Reg::Offset(reg1), Reg::Offset(*reg2)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
                    // LOAD LOAD LT_INT
                    (
                        Instr::LoadOffset(reg1),
                        Instr::LoadOffset(reg2),
                        // TODO: make this work for any dest not just top
                        Instr::LessThanInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
                        ret.push(Line::Instr {
                            instr: Instr::LessThanInt(
                                Reg::Top,
                                Reg::Offset(reg1),
                                Reg::Offset(*reg2),
                            ),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 3;
                        true
                    }
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
                    (Instr::PushInt(a), Instr::PushInt(b), Instr::SubtractInt) => {
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

fn peephole4_helper(lines: &[Line], index: &mut usize, ret: &mut Vec<Line>) -> bool {
    match lines[*index].clone() {
        Line::Label(_) => false,
        Line::Instr {
            instr: instr1,
            lineno,
            file_id,
            func_id,
        } => {
            // WINDOW SIZE 4
            if *index + 3 < lines.len()
                && let Line::Instr { instr: instr2, .. } = &lines[*index + 1]
                && let Line::Instr { instr: instr3, .. } = &lines[*index + 2]
                && let Line::Instr { instr: instr4, .. } = &lines[*index + 3]
            {
                match (instr1, instr2, instr3, instr4) {
                    // LOAD(X) PUSH(n) ADD_INT STORE(X) -> INCR(X)
                    (
                        Instr::LoadOffset(reg1),
                        Instr::PushInt(n),
                        Instr::AddInt(Reg::Top, Reg::Top, Reg::Top),
                        Instr::StoreOffset(reg2),
                    ) if reg1 == *reg2 && fits_imm(*n) => {
                        ret.push(Line::Instr {
                            instr: Instr::IncrementRegImm(reg1, as_imm(*n)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 4;
                        true
                    }
                    // LOAD(X) PUSH(n) SUB_INT STORE(X) -> INCR(X)
                    (
                        Instr::LoadOffset(reg1),
                        Instr::PushInt(n),
                        Instr::SubtractInt,
                        Instr::StoreOffset(reg2),
                    ) if reg1 == *reg2 && fits_imm(-n) => {
                        ret.push(Line::Instr {
                            instr: Instr::IncrementRegImm(reg1, as_imm(-n)),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 4;
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

impl Instr {
    fn second_arg_is_top(&self) -> bool {
        match self {
            Instr::AddInt(_, _, Reg::Top) => true,
            _ => false,
        }
    }
    fn first_arg_is_top_and_second_arg_is_offset(&self) -> bool {
        match self {
            Instr::AddInt(_, Reg::Top, Reg::Offset(_)) => true,
            _ => false,
        }
    }

    fn dest_is_top(&self) -> bool {
        match self {
            Instr::AddInt(Reg::Top, _, _) => true,
            _ => false,
        }
    }

    fn replace_first_arg(self, r1: Reg) -> Instr {
        match self {
            Instr::AddInt(dest, _, r2) => Instr::AddInt(dest, r1, r2),
            _ => self,
        }
    }

    fn replace_second_arg(self, r2: Reg) -> Instr {
        match self {
            Instr::AddInt(dest, r1, _) => Instr::AddInt(dest, r1, r2),
            _ => self,
        }
    }

    fn replace_dest(self, dest: Reg) -> Instr {
        match self {
            Instr::AddInt(_, r1, r2) => Instr::AddInt(dest, r1, r2),
            _ => self,
        }
    }
}
