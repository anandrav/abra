enum Instr {
    ADD,
    SUB,
    MUL,

    PUSH(i64),
    JUMP(i64),
    JUMP_IF_ZERO(i64),

    CALL(i64),
    RET,

    HALT,
}

struct Machine {
    code: Vec<Instr>,
    stack: Vec<i64>,
    call_stack: Vec<usize>,
    heap: Vec<Expr>,
    ip: usize,
}

impl Machine {
    fn step(&mut self) {
        let instr = self.code[self.ip];
        self.ip += 1;

        match instr {
            Instr::ADD => {
                let b = self.stack.pop().unwrap();
                let a = self.stack.pop().unwrap();
                self.stack.push(a + b);
            }
            Instr::SUB => {
                let b = self.stack.pop().unwrap();
                let a = self.stack.pop().unwrap();
                self.stack.push(a - b);
            }
            Instr::MUL => {
                let b = self.stack.pop().unwrap();
                let a = self.stack.pop().unwrap();
                self.stack.push(a * b);
            }
            Instr::PUSH(n) => {
                self.stack.push(n);
            }
            Instr::JUMP(addr) => {
                self.ip = addr as usize;
            }
            Instr::JUMP_IF_ZERO(addr) => {
                if self.stack.pop().unwrap() == 0 {
                    self.ip = addr as usize;
                }
            }
            Instr::CALL(addr) => {
                self.call_stack.push(self.ip);
                self.ip = addr as usize;
            }
            Instr::RET => {
                self.ip = self.call_stack.pop().unwrap();
            }
            Instr::HALT => {
                return;
            }
        }
    }
}
