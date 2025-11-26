/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::assembly::{Instr, Line, Reg};
use crate::vm::AbraInt;

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
                    // PUSH TRUE JUMP_IF
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
                    // PUSH TRUE JUMP_IF_FALSE
                    (Instr::PushBool(true), Instr::JumpIfFalse(_)) => {
                        *index += 2;
                        true
                    }
                    // PUSH FALSE JUMP_IF
                    (Instr::PushBool(false), Instr::JumpIf(_)) => {
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
                    // PUSHINT STORE -> STORE IMM
                    (Instr::PushInt(n), Instr::StoreOffset(offset)) => {
                        ret.push(Line::Instr {
                            instr: Instr::StoreOffsetImm(*offset, n),
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
                        if instr1.is_push_imm_int()
                            && instr2.second_arg_is_top()
                            && instr2.can_replace_second_arg_with_imm_int() =>
                    {
                        ret.push(Line::Instr {
                            instr: instr2
                                .clone()
                                .replace_second_arg_imm_int(instr1.get_imm_int()),
                            lineno,
                            file_id,
                            func_id,
                        });
                        *index += 2; // TODO: doing + 2 everywhere is redundant and error prone. fix here and in other peephole functions
                        true
                    }
                    // PUSHFLOAT(N) ADD_FLOAT(_, _, TOP) -> ADD_FLOAT_IMM(_, _, N)
                    (instr1, instr2)
                        if instr1.is_push_imm_float()
                            && instr2.second_arg_is_top()
                            && instr2.can_replace_second_arg_with_imm_float() =>
                    {
                        ret.push(Line::Instr {
                            instr: instr2
                                .clone()
                                .replace_second_arg_imm_float(instr1.get_imm_float()),
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
                    (
                        Instr::PushInt(a),
                        Instr::PushInt(b),
                        Instr::DivInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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
                    (
                        Instr::PushInt(a),
                        Instr::PushInt(b),
                        Instr::PowInt(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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
                    (
                        Instr::PushFloat(a),
                        Instr::PushFloat(b),
                        Instr::AddFloat(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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
                    (
                        Instr::PushFloat(a),
                        Instr::PushFloat(b),
                        Instr::SubFloat(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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
                    (
                        Instr::PushFloat(a),
                        Instr::PushFloat(b),
                        Instr::MulFloat(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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
                    (
                        Instr::PushFloat(a),
                        Instr::PushFloat(b),
                        Instr::DivFloat(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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
                    (
                        Instr::PushFloat(a),
                        Instr::PushFloat(b),
                        Instr::PowFloat(Reg::Top, Reg::Top, Reg::Top),
                    ) => {
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

// fn as_imm_bool(b: bool) -> i16 {
//     if b { 1 } else { 0 }
// }

impl Instr {
    fn second_arg_is_top(&self) -> bool {
        matches!(
            self,
            Instr::AddInt(_, _, Reg::Top)
                | Instr::SubInt(_, _, Reg::Top)
                | Instr::MulInt(_, _, Reg::Top)
                | Instr::DivInt(_, _, Reg::Top)
                | Instr::PowInt(_, _, Reg::Top)
                | Instr::Modulo(_, _, Reg::Top)
                | Instr::AddFloat(_, _, Reg::Top)
                | Instr::SubFloat(_, _, Reg::Top)
                | Instr::MulFloat(_, _, Reg::Top)
                | Instr::DivFloat(_, _, Reg::Top)
                | Instr::PowFloat(_, _, Reg::Top)
                | Instr::SquareRoot(_, Reg::Top)
                | Instr::LessThanInt(_, _, Reg::Top)
                | Instr::LessThanOrEqualInt(_, _, Reg::Top)
                | Instr::GreaterThanInt(_, _, Reg::Top)
                | Instr::GreaterThanOrEqualInt(_, _, Reg::Top)
                | Instr::EqualInt(_, _, Reg::Top)
                | Instr::LessThanFloat(_, _, Reg::Top)
                | Instr::LessThanOrEqualFloat(_, _, Reg::Top)
                | Instr::GreaterThanFloat(_, _, Reg::Top)
                | Instr::GreaterThanOrEqualFloat(_, _, Reg::Top)
                | Instr::EqualFloat(_, _, Reg::Top)
                | Instr::ArrayPush(_, Reg::Top)
                | Instr::ArrayLength(_, Reg::Top)
                | Instr::ArrayPop(_, Reg::Top)
                | Instr::GetIdx(_, Reg::Top)
                | Instr::SetIdx(_, Reg::Top)
                | Instr::GetField(_, Reg::Top)
                | Instr::SetField(_, Reg::Top)
        )
    }
    fn first_arg_is_top_and_second_arg_is_offset_or_imm(&self) -> bool {
        matches!(
            self,
            Instr::AddInt(_, Reg::Top, Reg::Offset(_))
                | Instr::AddIntImm(_, Reg::Top, _)
                | Instr::SubInt(_, Reg::Top, Reg::Offset(_))
                | Instr::SubIntImm(_, Reg::Top, _)
                | Instr::MulInt(_, Reg::Top, Reg::Offset(_))
                | Instr::MulIntImm(_, Reg::Top, _)
                | Instr::DivInt(_, Reg::Top, Reg::Offset(_))
                | Instr::DivIntImm(_, Reg::Top, _)
                | Instr::PowInt(_, Reg::Top, Reg::Offset(_))
                | Instr::PowIntImm(_, Reg::Top, _)
                | Instr::Modulo(_, Reg::Top, Reg::Offset(_))
                | Instr::ModuloImm(_, Reg::Top, _)
                | Instr::AddFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::AddFloatImm(_, Reg::Top, _)
                | Instr::SubFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::SubFloatImm(_, Reg::Top, _)
                | Instr::MulFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::MulFloatImm(_, Reg::Top, _)
                | Instr::DivFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::DivFloatImm(_, Reg::Top, _)
                | Instr::PowFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::PowFloat(_, Reg::Top, _)
                | Instr::LessThanInt(_, Reg::Top, Reg::Offset(_))
                | Instr::LessThanIntImm(_, Reg::Top, _)
                | Instr::LessThanOrEqualInt(_, Reg::Top, Reg::Offset(_))
                | Instr::LessThanOrEqualIntImm(_, Reg::Top, _)
                | Instr::GreaterThanInt(_, Reg::Top, Reg::Offset(_))
                | Instr::GreaterThanOrEqualIntImm(_, Reg::Top, _)
                | Instr::EqualInt(_, Reg::Top, Reg::Offset(_))
                | Instr::EqualIntImm(_, Reg::Top, _)
                | Instr::LessThanFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::LessThanFloatImm(_, Reg::Top, _)
                | Instr::LessThanOrEqualFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::LessThanOrEqualFloatImm(_, Reg::Top, _)
                | Instr::GreaterThanFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::GreaterThanOrEqualFloatImm(_, Reg::Top, _)
                | Instr::EqualFloat(_, Reg::Top, Reg::Offset(_))
                | Instr::EqualFloatImm(_, Reg::Top, _)
                | Instr::ArrayPush(Reg::Top, Reg::Offset(_))
                | Instr::ArrayPushIntImm(Reg::Top, _)
                | Instr::GetIdx(Reg::Top, Reg::Offset(_))
                | Instr::SetIdx(Reg::Top, _)
        )
    }

    fn dest_is_top(&self) -> bool {
        matches!(
            self,
            Instr::AddInt(Reg::Top, _, _)
                | Instr::AddIntImm(Reg::Top, _, _)
                | Instr::SubInt(Reg::Top, _, _)
                | Instr::SubIntImm(Reg::Top, _, _)
                | Instr::MulInt(Reg::Top, _, _)
                | Instr::MulIntImm(Reg::Top, _, _)
                | Instr::DivInt(Reg::Top, _, _)
                | Instr::DivIntImm(Reg::Top, _, _)
                | Instr::PowInt(Reg::Top, _, _)
                | Instr::PowIntImm(Reg::Top, _, _)
                | Instr::Modulo(Reg::Top, _, _)
                | Instr::ModuloImm(Reg::Top, _, _)
                | Instr::AddFloat(Reg::Top, _, _)
                | Instr::AddFloatImm(Reg::Top, _, _)
                | Instr::SubFloat(Reg::Top, _, _)
                | Instr::SubFloatImm(Reg::Top, _, _)
                | Instr::MulFloat(Reg::Top, _, _)
                | Instr::MulFloatImm(Reg::Top, _, _)
                | Instr::DivFloat(Reg::Top, _, _)
                | Instr::DivFloatImm(Reg::Top, _, _)
                | Instr::PowFloat(Reg::Top, _, _)
                | Instr::PowFloatImm(Reg::Top, _, _)
                | Instr::SquareRoot(Reg::Top, _)
                | Instr::LessThanInt(Reg::Top, _, _)
                | Instr::LessThanIntImm(Reg::Top, _, _)
                | Instr::LessThanOrEqualInt(Reg::Top, _, _)
                | Instr::LessThanOrEqualIntImm(Reg::Top, _, _)
                | Instr::GreaterThanInt(Reg::Top, _, _)
                | Instr::GreaterThanIntImm(Reg::Top, _, _)
                | Instr::GreaterThanOrEqualInt(Reg::Top, _, _)
                | Instr::GreaterThanOrEqualIntImm(Reg::Top, _, _)
                | Instr::EqualInt(Reg::Top, _, _)
                | Instr::EqualIntImm(Reg::Top, _, _)
                | Instr::LessThanFloat(Reg::Top, _, _)
                | Instr::LessThanFloatImm(Reg::Top, _, _)
                | Instr::LessThanOrEqualFloat(Reg::Top, _, _)
                | Instr::LessThanOrEqualFloatImm(Reg::Top, _, _)
                | Instr::GreaterThanFloat(Reg::Top, _, _)
                | Instr::GreaterThanFloatImm(Reg::Top, _, _)
                | Instr::GreaterThanOrEqualFloat(Reg::Top, _, _)
                | Instr::GreaterThanOrEqualFloatImm(Reg::Top, _, _)
                | Instr::EqualFloat(Reg::Top, _, _)
                | Instr::EqualFloatImm(Reg::Top, _, _)
                | Instr::ArrayPop(Reg::Top, _)
                | Instr::ArrayLength(Reg::Top, _)
        )
    }

    fn replace_first_arg(self, r1: Reg) -> Instr {
        match self {
            Instr::AddInt(dest, _, r2) => Instr::AddInt(dest, r1, r2),
            Instr::AddIntImm(dest, _, r2) => Instr::AddIntImm(dest, r1, r2),
            Instr::SubInt(dest, _, r2) => Instr::SubInt(dest, r1, r2),
            Instr::SubIntImm(dest, _, r2) => Instr::SubIntImm(dest, r1, r2),
            Instr::MulInt(dest, _, r2) => Instr::MulInt(dest, r1, r2),
            Instr::MulIntImm(dest, _, r2) => Instr::MulIntImm(dest, r1, r2),
            Instr::DivInt(dest, _, r2) => Instr::DivInt(dest, r1, r2),
            Instr::DivIntImm(dest, _, r2) => Instr::DivIntImm(dest, r1, r2),
            Instr::PowInt(dest, _, r2) => Instr::PowInt(dest, r1, r2),
            Instr::PowIntImm(dest, _, r2) => Instr::PowIntImm(dest, r1, r2),
            Instr::Modulo(dest, _, r2) => Instr::Modulo(dest, r1, r2),
            Instr::ModuloImm(dest, _, r2) => Instr::ModuloImm(dest, r1, r2),

            Instr::AddFloat(dest, _, r2) => Instr::AddFloat(dest, r1, r2),
            Instr::AddFloatImm(dest, _, r2) => Instr::AddFloatImm(dest, r1, r2),
            Instr::SubFloat(dest, _, r2) => Instr::SubFloat(dest, r1, r2),
            Instr::SubFloatImm(dest, _, r2) => Instr::SubFloatImm(dest, r1, r2),
            Instr::MulFloat(dest, _, r2) => Instr::MulFloat(dest, r1, r2),
            Instr::MulFloatImm(dest, _, r2) => Instr::MulFloatImm(dest, r1, r2),
            Instr::DivFloat(dest, _, r2) => Instr::DivFloat(dest, r1, r2),
            Instr::DivFloatImm(dest, _, r2) => Instr::DivFloatImm(dest, r1, r2),
            Instr::PowFloat(dest, _, r2) => Instr::PowFloat(dest, r1, r2),
            Instr::PowFloatImm(dest, _, r2) => Instr::PowFloatImm(dest, r1, r2),

            Instr::LessThanInt(dest, _, r2) => Instr::LessThanInt(dest, r1, r2),
            Instr::LessThanIntImm(dest, _, r2) => Instr::LessThanIntImm(dest, r1, r2),
            Instr::LessThanOrEqualInt(dest, _, r2) => Instr::LessThanOrEqualInt(dest, r1, r2),
            Instr::LessThanOrEqualIntImm(dest, _, r2) => Instr::LessThanOrEqualIntImm(dest, r1, r2),
            Instr::GreaterThanInt(dest, _, r2) => Instr::GreaterThanInt(dest, r1, r2),
            Instr::GreaterThanIntImm(dest, _, r2) => Instr::GreaterThanIntImm(dest, r1, r2),
            Instr::GreaterThanOrEqualInt(dest, _, r2) => Instr::GreaterThanOrEqualInt(dest, r1, r2),
            Instr::GreaterThanOrEqualIntImm(dest, _, r2) => {
                Instr::GreaterThanOrEqualIntImm(dest, r1, r2)
            }

            Instr::EqualInt(dest, _, r2) => Instr::EqualInt(dest, r1, r2),
            Instr::EqualIntImm(dest, _, r2) => Instr::EqualIntImm(dest, r1, r2),

            Instr::LessThanFloat(dest, _, r2) => Instr::LessThanFloat(dest, r1, r2),
            Instr::LessThanFloatImm(dest, _, r2) => Instr::LessThanFloatImm(dest, r1, r2),
            Instr::LessThanOrEqualFloat(dest, _, r2) => Instr::LessThanOrEqualFloat(dest, r1, r2),
            Instr::LessThanOrEqualFloatImm(dest, _, r2) => {
                Instr::LessThanOrEqualFloatImm(dest, r1, r2)
            }
            Instr::GreaterThanFloat(dest, _, r2) => Instr::GreaterThanFloat(dest, r1, r2),
            Instr::GreaterThanFloatImm(dest, _, r2) => Instr::GreaterThanFloatImm(dest, r1, r2),
            Instr::GreaterThanOrEqualFloat(dest, _, r2) => {
                Instr::GreaterThanOrEqualFloat(dest, r1, r2)
            }
            Instr::GreaterThanOrEqualFloatImm(dest, _, r2) => {
                Instr::GreaterThanOrEqualFloatImm(dest, r1, r2)
            }

            Instr::EqualFloat(dest, _, r2) => Instr::EqualFloat(dest, r1, r2),
            Instr::EqualFloatImm(dest, _, r2) => Instr::EqualFloatImm(dest, r1, r2),

            Instr::ArrayPush(_, r2) => Instr::ArrayPush(r1, r2),
            Instr::ArrayPushIntImm(_, r2) => Instr::ArrayPushIntImm(r1, r2),
            Instr::GetIdx(_, r2) => Instr::GetIdx(r1, r2),
            Instr::SetIdx(_, r2) => Instr::SetIdx(r1, r2),

            _ => panic!("can't replace first arg"),
        }
    }

    fn replace_second_arg(self, r2: Reg) -> Instr {
        match self {
            Instr::AddInt(dest, r1, _) => Instr::AddInt(dest, r1, r2),
            Instr::SubInt(dest, r1, _) => Instr::SubInt(dest, r1, r2),
            Instr::MulInt(dest, r1, _) => Instr::MulInt(dest, r1, r2),
            Instr::DivInt(dest, r1, _) => Instr::DivInt(dest, r1, r2),
            Instr::PowInt(dest, r1, _) => Instr::PowInt(dest, r1, r2),
            Instr::Modulo(dest, r1, _) => Instr::Modulo(dest, r1, r2),

            Instr::AddFloat(dest, r1, _) => Instr::AddFloat(dest, r1, r2),
            Instr::SubFloat(dest, r1, _) => Instr::SubFloat(dest, r1, r2),
            Instr::MulFloat(dest, r1, _) => Instr::MulFloat(dest, r1, r2),
            Instr::DivFloat(dest, r1, _) => Instr::DivFloat(dest, r1, r2),
            Instr::PowFloat(dest, r1, _) => Instr::PowFloat(dest, r1, r2),
            Instr::SquareRoot(dest, _) => Instr::SquareRoot(dest, r2),

            Instr::LessThanInt(dest, r1, _) => Instr::LessThanInt(dest, r1, r2),
            Instr::LessThanOrEqualInt(dest, r1, _) => Instr::LessThanOrEqualInt(dest, r1, r2),
            Instr::GreaterThanInt(dest, r1, _) => Instr::GreaterThanInt(dest, r1, r2),
            Instr::GreaterThanOrEqualInt(dest, r1, _) => Instr::GreaterThanOrEqualInt(dest, r1, r2),

            Instr::EqualInt(dest, r1, _) => Instr::EqualInt(dest, r1, r2),

            Instr::LessThanFloat(dest, r1, _) => Instr::LessThanFloat(dest, r1, r2),
            Instr::LessThanOrEqualFloat(dest, r1, _) => Instr::LessThanOrEqualFloat(dest, r1, r2),
            Instr::GreaterThanFloat(dest, r1, _) => Instr::GreaterThanFloat(dest, r1, r2),
            Instr::GreaterThanOrEqualFloat(dest, r1, _) => {
                Instr::GreaterThanOrEqualFloat(dest, r1, r2)
            }

            Instr::EqualFloat(dest, r1, _) => Instr::EqualFloat(dest, r1, r2),

            Instr::ArrayPush(r1, _) => Instr::ArrayPush(r1, r2),
            Instr::ArrayLength(dest, _) => Instr::ArrayLength(dest, r2),
            Instr::ArrayPop(dest, _) => Instr::ArrayPop(dest, r2),
            Instr::GetIdx(r1, _) => Instr::GetIdx(r1, r2),
            Instr::SetIdx(r1, _) => Instr::SetIdx(r1, r2),
            Instr::GetField(idx, _) => Instr::GetField(idx, r2),
            Instr::SetField(idx, _) => Instr::SetField(idx, r2),

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
            Instr::MulIntImm(_, r1, r2) => Instr::MulIntImm(dest, r1, r2),
            Instr::DivInt(_, r1, r2) => Instr::DivInt(dest, r1, r2),
            Instr::DivIntImm(_, r1, r2) => Instr::DivIntImm(dest, r1, r2),
            Instr::PowInt(_, r1, r2) => Instr::PowInt(dest, r1, r2),
            Instr::PowIntImm(_, r1, r2) => Instr::PowIntImm(dest, r1, r2),
            Instr::Modulo(_, r1, r2) => Instr::Modulo(dest, r1, r2),
            Instr::ModuloImm(_, r1, r2) => Instr::ModuloImm(dest, r1, r2),

            Instr::AddFloat(_, r1, r2) => Instr::AddFloat(dest, r1, r2),
            Instr::AddFloatImm(_, r1, r2) => Instr::AddFloatImm(dest, r1, r2),
            Instr::SubFloat(_, r1, r2) => Instr::SubFloat(dest, r1, r2),
            Instr::SubFloatImm(_, r1, r2) => Instr::SubFloatImm(dest, r1, r2),
            Instr::MulFloat(_, r1, r2) => Instr::MulFloat(dest, r1, r2),
            Instr::MulFloatImm(_, r1, r2) => Instr::MulFloatImm(dest, r1, r2),
            Instr::DivFloat(_, r1, r2) => Instr::DivFloat(dest, r1, r2),
            Instr::DivFloatImm(_, r1, r2) => Instr::DivFloatImm(dest, r1, r2),
            Instr::PowFloat(_, r1, r2) => Instr::PowFloat(dest, r1, r2),
            Instr::PowFloatImm(_, r1, r2) => Instr::PowFloatImm(dest, r1, r2),
            Instr::SquareRoot(_, r2) => Instr::SquareRoot(dest, r2),

            Instr::LessThanInt(_, r1, r2) => Instr::LessThanInt(dest, r1, r2),
            Instr::LessThanIntImm(_, r1, r2) => Instr::LessThanIntImm(dest, r1, r2),
            Instr::LessThanOrEqualInt(_, r1, r2) => Instr::LessThanOrEqualInt(dest, r1, r2),
            Instr::LessThanOrEqualIntImm(_, r1, r2) => Instr::LessThanOrEqualIntImm(dest, r1, r2),
            Instr::GreaterThanInt(_, r1, r2) => Instr::GreaterThanInt(dest, r1, r2),
            Instr::GreaterThanIntImm(_, r1, r2) => Instr::GreaterThanIntImm(dest, r1, r2),
            Instr::GreaterThanOrEqualInt(_, r1, r2) => Instr::GreaterThanOrEqualInt(dest, r1, r2),
            Instr::GreaterThanOrEqualIntImm(_, r1, r2) => {
                Instr::GreaterThanOrEqualIntImm(dest, r1, r2)
            }
            Instr::EqualInt(_, r1, r2) => Instr::EqualInt(dest, r1, r2),
            Instr::EqualIntImm(_, r1, r2) => Instr::EqualIntImm(dest, r1, r2),

            Instr::LessThanFloat(_, r1, r2) => Instr::LessThanFloat(dest, r1, r2),
            Instr::LessThanFloatImm(_, r1, r2) => Instr::LessThanFloatImm(dest, r1, r2),
            Instr::LessThanOrEqualFloat(_, r1, r2) => Instr::LessThanOrEqualFloat(dest, r1, r2),
            Instr::LessThanOrEqualFloatImm(_, r1, r2) => {
                Instr::LessThanOrEqualFloatImm(dest, r1, r2)
            }
            Instr::GreaterThanFloat(_, r1, r2) => Instr::GreaterThanFloat(dest, r1, r2),
            Instr::GreaterThanFloatImm(_, r1, r2) => Instr::GreaterThanFloatImm(dest, r1, r2),
            Instr::GreaterThanOrEqualFloat(_, r1, r2) => {
                Instr::GreaterThanOrEqualFloat(dest, r1, r2)
            }
            Instr::GreaterThanOrEqualFloatImm(_, r1, r2) => {
                Instr::GreaterThanOrEqualFloatImm(dest, r1, r2)
            }
            Instr::EqualFloat(_, r1, r2) => Instr::EqualFloat(dest, r1, r2),
            Instr::EqualFloatImm(_, r1, r2) => Instr::EqualFloatImm(dest, r1, r2),
            Instr::ArrayPop(_, r2) => Instr::ArrayPop(dest, r2),
            Instr::ArrayLength(_, r2) => Instr::ArrayLength(dest, r2),
            _ => panic!("can't replace dest"),
        }
    }

    fn is_push_imm_int(&self) -> bool {
        matches!(self, Instr::PushInt(_))
    }

    fn is_push_imm_float(&self) -> bool {
        matches!(self, Instr::PushFloat(_))
    }

    fn get_imm_int(&self) -> AbraInt {
        match self {
            Instr::PushInt(n) => *n,
            // Instr::PushBool(b) => as_imm_bool(*b), // boolean immediates are represented as int immediates
            _ => panic!("can't get immediate"),
        }
    }

    fn get_imm_float(&self) -> String {
        match self {
            Instr::PushFloat(n) => n.clone(),
            _ => panic!("can't get immediate"),
        }
    }

    fn can_replace_second_arg_with_imm_int(&self) -> bool {
        matches!(
            self,
            Instr::AddInt(..)
                | Instr::SubInt(..)
                | Instr::MulInt(..)
                | Instr::DivInt(..)
                | Instr::PowInt(..)
                | Instr::Modulo(..)
                | Instr::LessThanInt(..)
                | Instr::LessThanOrEqualInt(..)
                | Instr::GreaterThanInt(..)
                | Instr::GreaterThanOrEqualInt(..)
                | Instr::EqualInt(..)
                | Instr::ArrayPush(..)
        )
    }

    fn can_replace_second_arg_with_imm_float(&self) -> bool {
        matches!(
            self,
            Instr::AddFloat(..)
                | Instr::SubFloat(..)
                | Instr::MulFloat(..)
                | Instr::DivFloat(..)
                | Instr::PowFloat(..)
                | Instr::LessThanFloat(..)
                | Instr::LessThanOrEqualFloat(..)
                | Instr::GreaterThanFloat(..)
                | Instr::GreaterThanOrEqualFloat(..)
                | Instr::EqualFloat(..) // | Instr::ArrayPush(..) // TODO: would be nice if worked for floats... and bools...
        )
    }

    fn replace_second_arg_imm_int(self, imm: AbraInt) -> Instr {
        match self {
            Instr::AddInt(dest, r1, _) => Instr::AddIntImm(dest, r1, imm),
            Instr::SubInt(dest, r1, _) => Instr::SubIntImm(dest, r1, imm),
            Instr::MulInt(dest, r1, _) => Instr::MulIntImm(dest, r1, imm),
            Instr::DivInt(dest, r1, _) => Instr::DivIntImm(dest, r1, imm),
            Instr::PowInt(dest, r1, _) => Instr::PowIntImm(dest, r1, imm),
            Instr::Modulo(dest, r1, _) => Instr::ModuloImm(dest, r1, imm),
            Instr::LessThanInt(dest, r1, _) => Instr::LessThanIntImm(dest, r1, imm),
            Instr::LessThanOrEqualInt(dest, r1, _) => Instr::LessThanOrEqualIntImm(dest, r1, imm),
            Instr::GreaterThanInt(dest, r1, _) => Instr::GreaterThanIntImm(dest, r1, imm),
            Instr::GreaterThanOrEqualInt(dest, r1, _) => {
                Instr::GreaterThanOrEqualIntImm(dest, r1, imm)
            }
            Instr::EqualInt(dest, r1, _) => Instr::EqualIntImm(dest, r1, imm),
            Instr::ArrayPush(r1, _) => Instr::ArrayPushIntImm(r1, imm),
            _ => panic!("can't replace second arg with immediate"),
        }
    }

    fn replace_second_arg_imm_float(self, imm: String) -> Instr {
        match self {
            Instr::AddFloat(dest, r1, _) => Instr::AddFloatImm(dest, r1, imm),
            Instr::SubFloat(dest, r1, _) => Instr::SubFloatImm(dest, r1, imm),
            Instr::MulFloat(dest, r1, _) => Instr::MulFloatImm(dest, r1, imm),
            Instr::DivFloat(dest, r1, _) => Instr::DivFloatImm(dest, r1, imm),
            Instr::PowFloat(dest, r1, _) => Instr::PowFloatImm(dest, r1, imm),
            Instr::LessThanFloat(dest, r1, _) => Instr::LessThanFloatImm(dest, r1, imm),
            Instr::LessThanOrEqualFloat(dest, r1, _) => {
                Instr::LessThanOrEqualFloatImm(dest, r1, imm)
            }
            Instr::GreaterThanFloat(dest, r1, _) => Instr::GreaterThanFloatImm(dest, r1, imm),
            Instr::GreaterThanOrEqualFloat(dest, r1, _) => {
                Instr::GreaterThanOrEqualFloatImm(dest, r1, imm)
            }
            Instr::EqualFloat(dest, r1, _) => Instr::EqualFloatImm(dest, r1, imm),
            _ => panic!("can't replace second arg with immediate float"),
        }
    }
}
