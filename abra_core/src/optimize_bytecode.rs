/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */
use crate::assembly::{Instr, Line};

pub(crate) fn optimize(lines: Vec<Line>) -> Vec<Line> {
    let mut len = lines.len();
    let mut ret = lines;
    loop {
        // TODO: combine these into a sigle peephole function. Have a bias for larger windows (3 then 2 then 1)
        ret = peephole3(ret);
        ret = peephole2(ret);
        ret = peephole1(ret);
        if ret.len() < len {
            len = ret.len();
        } else {
            break;
        }
    }
    ret
}

pub(crate) fn peephole1(lines: Vec<Line>) -> Vec<Line> {
    let mut ret: Vec<Line> = vec![];

    let mut index = 0;
    while index < lines.len() {
        let curr = &lines[index];
        match lines[index].clone() {
            Line::Label(_) => {
                // noop
                ret.push(curr.clone());
                index += 1;
            }
            Line::Instr {
                instr: instr1,
                lineno: _,
                file_id: _,
                func_id: _,
            } => {
                let mut noop = |index: &mut usize| {
                    ret.push(curr.clone());
                    *index += 1;
                };

                match instr1 {
                    // PUSH 0
                    Instr::PushNil(0) => {
                        index += 1;
                    }
                    _ => {
                        noop(&mut index);
                    }
                }
            }
        }
    }

    ret
}

pub(crate) fn peephole2(lines: Vec<Line>) -> Vec<Line> {
    let mut ret: Vec<Line> = vec![];

    let mut index = 0;
    while index < lines.len() {
        let curr = &lines[index];
        match lines[index].clone() {
            Line::Label(_) => {
                // noop
                ret.push(curr.clone());
                index += 1;
            }
            Line::Instr {
                instr: instr1,
                lineno,
                file_id,
                func_id,
            } => {
                let mut noop = |index: &mut usize| {
                    ret.push(curr.clone());
                    *index += 1;
                };
                if index + 1 < lines.len()
                    && let Line::Instr { instr: instr2, .. } = &lines[index + 1]
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
                            index += 2;
                        }
                        (
                            Instr::PushBool(_)
                            | Instr::PushFloat(_)
                            | Instr::PushInt(_)
                            | Instr::PushString(_),
                            Instr::Pop,
                        ) => {
                            index += 2;
                        }
                        (Instr::Duplicate, Instr::Pop) => {
                            index += 2;
                        }
                        // NOT JUMP_IF -> JUMP_IF_FALSE
                        (Instr::Not, Instr::JumpIf(label)) => {
                            ret.push(Line::Instr {
                                instr: Instr::JumpIfFalse(label.clone()),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 2;
                        }
                        // PUSH TRUE JUMP IF
                        (Instr::PushBool(true), Instr::JumpIf(label)) => {
                            ret.push(Line::Instr {
                                instr: Instr::Jump(label.clone()),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 2;
                        }
                        // BOOLEAN FLIP
                        (Instr::PushBool(b), Instr::Not) => {
                            ret.push(Line::Instr {
                                instr: Instr::PushBool(!b),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 2;
                        }
                        // // LOADOFFSET GETFIELD
                        (Instr::LoadOffset(offset), Instr::GetField(field)) => {
                            ret.push(Line::Instr {
                                instr: Instr::GetFieldOffset(*field, offset),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 2;
                        }
                        // LOADOFFSET SETFIELD
                        (Instr::LoadOffset(offset), Instr::SetField(field)) => {
                            ret.push(Line::Instr {
                                instr: Instr::SetFieldOffset(*field, offset),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 2;
                        }
                        _ => {
                            noop(&mut index);
                        }
                    }
                } else {
                    noop(&mut index);
                }
            }
        }
    }

    ret
}

pub(crate) fn peephole3(lines: Vec<Line>) -> Vec<Line> {
    let mut ret: Vec<Line> = vec![];

    let mut index = 0;
    while index < lines.len() {
        let curr = &lines[index];
        match lines[index].clone() {
            Line::Label(_) => {
                // noop
                ret.push(curr.clone());
                index += 1;
            }
            Line::Instr {
                instr: instr1,
                lineno,
                file_id,
                func_id,
            } => {
                let mut noop = |index: &mut usize| {
                    ret.push(curr.clone());
                    *index += 1;
                };
                // WINDOW SIZE 3
                if index + 2 < lines.len()
                    && let Line::Instr { instr: instr2, .. } = &lines[index + 1]
                    && let Line::Instr { instr: instr3, .. } = &lines[index + 2]
                {
                    match (instr1, instr2, instr3) {
                        // LOAD LOAD ADD_INT
                        (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::AddInt) => {
                            ret.push(Line::Instr {
                                instr: Instr::AddIntReg(reg1, *reg2),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
                        }
                        // LOAD LOAD MUL_INT
                        (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::MultiplyInt) => {
                            ret.push(Line::Instr {
                                instr: Instr::MultiplyIntReg(reg1, *reg2),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
                        }
                        // LOAD LOAD LT_INT
                        (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::LessThanInt) => {
                            ret.push(Line::Instr {
                                instr: Instr::LessThanIntReg(reg1, *reg2),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
                        }
                        // LOAD LOAD GET_INDEX
                        (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::GetIdx) => {
                            ret.push(Line::Instr {
                                instr: Instr::GetIdxOffset(reg1, *reg2),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
                        }
                        // LOAD LOAD SET_INDEX
                        (Instr::LoadOffset(reg1), Instr::LoadOffset(reg2), Instr::SetIdx) => {
                            ret.push(Line::Instr {
                                instr: Instr::SetIdxOffset(reg1, *reg2),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
                        }
                        // FOLD INT ADDITION
                        (Instr::PushInt(a), Instr::PushInt(b), Instr::AddInt) => {
                            let c = a.wrapping_add(*b);
                            ret.push(Line::Instr {
                                instr: Instr::PushInt(c),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
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
                            index += 3;
                        }
                        // FOLD INT MULTIPLICATION
                        (Instr::PushInt(a), Instr::PushInt(b), Instr::MultiplyInt) => {
                            let c = a.wrapping_mul(*b);
                            ret.push(Line::Instr {
                                instr: Instr::PushInt(c),
                                lineno,
                                file_id,
                                func_id,
                            });
                            index += 3;
                        }
                        // FOLD INT DIVISION
                        (Instr::PushInt(a), Instr::PushInt(b), Instr::DivideInt) => {
                            if *b == 0 {
                                noop(&mut index);
                            } else {
                                let c = a.wrapping_div(*b);
                                ret.push(Line::Instr {
                                    instr: Instr::PushInt(c),
                                    lineno,
                                    file_id,
                                    func_id,
                                });
                                index += 3;
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
                            index += 3;
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
                            index += 3;
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
                            index += 3;
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
                            index += 3;
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
                            index += 3;
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
                            index += 3;
                        }
                        _ => {
                            noop(&mut index);
                        }
                    }
                } else {
                    noop(&mut index);
                }
            }
        }
    }

    ret
}
