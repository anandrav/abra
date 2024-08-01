type ProgramCounter = usize;
type Val = isize;

#[derive(Debug)]
pub struct Vm {
    program: Vec<Instr>,
    stack: Vec<Val>,
    pc: usize,
}

#[derive(Debug, Copy, Clone)]
enum Instr {
    Push(Val),
    Pop,
    Add,
    Sub,
    Mul,
    Div,

    Jump(usize),
    JumpIfNotZero(usize),

    Compare,
}

impl Vm {
    pub fn run(&mut self, steps: u32) {
        for _ in 0..steps {
            while let Some(instr) = self.program.get(self.pc).cloned() {
                match instr {
                    Instr::Push(value) => {
                        self.stack.push(value);
                    }
                    Instr::Pop => {
                        self.stack.pop();
                    }
                    Instr::Add => {
                        let a = self.arg();
                        let b = self.arg();
                        self.stack.push(a + b);
                    }
                    Instr::Sub => {
                        let a = self.arg();
                        let b = self.arg();
                        self.stack.push(a - b);
                    }
                    Instr::Mul => {
                        let a = self.arg();
                        let b = self.arg();
                        self.stack.push(a * b);
                    }
                    Instr::Div => {
                        let a = self.arg();
                        let b = self.arg();
                        self.stack.push(a / b);
                    }
                    Instr::Jump(target) => {
                        self.pc = target;
                        continue;
                    }
                    Instr::JumpIfNotZero(target) => {
                        let a = self.arg();
                        if a != 0 {
                            self.pc = target;
                            continue;
                        }
                    }
                    Instr::Compare => {
                        let a = self.arg();
                        let b = self.arg();
                        let result = match a.cmp(&b) {
                            std::cmp::Ordering::Greater => 1,
                            std::cmp::Ordering::Less => -1,
                            std::cmp::Ordering::Equal => 0,
                        };
                        self.stack.push(result);
                    }
                }
                self.pc += 1;
            }
        }
    }

    pub fn arg(&mut self) -> isize {
        self.stack.pop().expect("stack underflow")
    }
}
