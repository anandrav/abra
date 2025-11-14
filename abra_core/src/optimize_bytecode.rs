use crate::assembly::{Instr, Line};

pub(crate) fn optimize(lines: Vec<Line>) -> Vec<Line> {
    let mut len = lines.len();
    let mut ret = lines;
    loop {
        ret = peephole2(ret);
        ret = peephole3(ret);
        if ret.len() < len {
            len = ret.len();
        } else {
            break;
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
                        // PUSH 0
                        (Instr::PushNil(0), _) => {
                            index += 1;
                        }
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
                        // PUSH TRUE JUMP IF
                        // BOOLEAN FLIP
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

/*
   main:
   addint
   push
   pop
   fib:
   push 32
   pushnil
   pop
   branch
   foo:
   panic

*/
