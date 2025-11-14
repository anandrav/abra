use crate::assembly::{Instr, Line};

pub(crate) fn optimize(lines: Vec<Line>) -> Vec<Line> {
    let mut len = lines.len();
    let mut ret = lines;
    loop {
        ret = peephole(ret);
        if ret.len() < len {
            len = ret.len();
        } else {
            break;
        }
    }
    ret
}

pub(crate) fn peephole(lines: Vec<Line>) -> Vec<Line> {
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
                            // noop
                            ret.push(curr.clone());
                            index += 1;
                        }
                    }
                } else {
                    // noop
                    ret.push(curr.clone());
                    index += 1;
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
