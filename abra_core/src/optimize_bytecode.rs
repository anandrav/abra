use crate::assembly::{Instr, Line};

pub(crate) fn peephole(lines: Vec<Line>) -> Vec<Line> {
    let mut ret: Vec<Line> = vec![];

    let mut index = 0;
    while index < lines.len() {
        let curr = &lines[index];
        match &lines[index] {
            Line::Label(_) => {
                // noop
                ret.push(curr.clone());
                index += 1;
            }
            Line::Instr { instr: instr1, .. } => {
                if index + 1 < lines.len()
                    && let Line::Instr { instr: instr2, .. } = &lines[index + 1]
                {
                    match (instr1, instr2) {
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
