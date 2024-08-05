type ProgramCounter = usize;
use crate::assembly::assemble;

#[derive(Debug)]
pub struct Vm {
    program: Vec<u8>,
    pc: ProgramCounter,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    heap: Vec<ManagedObject>,
}

impl Vm {
    pub(crate) fn new(program: Vec<u8>) -> Self {
        Self {
            program,
            pc: 0,
            value_stack: Vec::new(),
            call_stack: Vec::new(),
            heap: Vec::new(),
        }
    }

    fn top(&self) -> &Value {
        self.value_stack.last().expect("stack underflow")
    }
}

#[derive(Debug, Copy, Clone)]
pub(crate) enum Instr {
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Return,
    PushBool(bool),
    PushInt(i64),
    Jump(ProgramCounter),
    JumpIfTrue(ProgramCounter),
    Call(ProgramCounter),
}

impl Instr {
    pub(crate) fn opcode(&self) -> u8 {
        match self {
            Instr::Pop => 0,
            Instr::Add => 1,
            Instr::Sub => 2,
            Instr::Mul => 3,
            Instr::Div => 4,
            Instr::Return => 5,
            Instr::PushBool(_) => 6,
            Instr::PushInt(_) => 7,
            Instr::Jump(_) => 8,
            Instr::JumpIfTrue(_) => 9,
            Instr::Call(_) => 10,
        }
    }

    pub(crate) fn size(&self) -> usize {
        let mut n = 1;
        match self {
            Instr::Pop | Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | Instr::Return => {}
            Instr::PushBool(_) => n += size_of::<bool>(),
            Instr::PushInt(_) => n += size_of::<i64>(),
            Instr::Jump(_) | Instr::JumpIfTrue(_) | Instr::Call(_) => n += size_of::<usize>(),
        }
        n
    }

    pub(crate) fn encode(&self, buf: &mut Vec<u8>) {
        buf.push(self.opcode());
        match self {
            Instr::PushBool(b) => {
                buf.push(*b as u8);
            }
            Instr::PushInt(n) => {
                buf.extend(n.to_le_bytes().iter());
            }
            Instr::Jump(target) | Instr::JumpIfTrue(target) | Instr::Call(target) => {
                buf.extend(target.to_le_bytes().iter());
            }
            _ => {}
        }
    }

    pub(crate) fn decode(buf: &[u8]) -> Self {
        match buf[0] {
            0 => Instr::Pop,
            1 => Instr::Add,
            2 => Instr::Sub,
            3 => Instr::Mul,
            4 => Instr::Div,
            5 => Instr::Return,
            6 => Instr::PushBool(buf[1] != 0),
            7 => Instr::PushInt(i64::from_le_bytes(buf[1..9].try_into().unwrap())),
            8 => Instr::Jump(usize::from_le_bytes(buf[1..9].try_into().unwrap())),
            9 => Instr::JumpIfTrue(usize::from_le_bytes(buf[1..9].try_into().unwrap())),
            10 => Instr::Call(usize::from_le_bytes(buf[1..9].try_into().unwrap())),
            _ => panic!("invalid opcode"),
        }
    }
}

impl Into<String> for Instr {
    fn into(self) -> String {
        match self {
            Instr::Pop => "pop".into(),
            Instr::Add => "add".into(),
            Instr::Sub => "sub".into(),
            Instr::Mul => "mul".into(),
            Instr::Div => "div".into(),
            Instr::Return => "ret".into(),
            Instr::PushBool(b) => format!("pushb {}", b),
            Instr::PushInt(n) => format!("pushi {}", n),
            Instr::Jump(loc) => format!("jump {}", loc),
            Instr::JumpIfTrue(loc) => format!("jumpif {}", loc),
            Instr::Call(loc) => format!("call {}", loc),
        }
    }
}

#[derive(Debug, Copy, Clone)]
enum Value {
    Bool(bool),
    Int(i64),
    ManagedObject(usize),
}

impl From<bool> for Value {
    fn from(b: bool) -> Value {
        Value::Bool(b)
    }
}

impl From<i64> for Value {
    fn from(n: i64) -> Value {
        Value::Int(n)
    }
}

impl Value {
    fn get_int(&self) -> i64 {
        match self {
            Value::Int(n) => *n,
            _ => panic!("not an int"),
        }
    }

    fn get_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            _ => panic!("not a bool"),
        }
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_base: usize,
}

// ReferenceType
// TODO: garbage collection (mark-and-sweep? copy-collection?)
#[derive(Debug)]
struct ManagedObject {
    // mark: bool,
    kind: ManagedObjectKind,
}

#[derive(Debug)]
enum ManagedObjectKind {
    Adt {
        tag: usize,
        fields: Vec<Value>,
    },
    Record(Vec<Value>),
    String(String),
    DynArray(Vec<Value>),
    FunctionObject {
        closure: Vec<Value>, /* TODO */
        addr: ProgramCounter,
    },
}

impl Vm {
    pub fn run(&mut self) {
        while self.pc < self.program.len() {
            self.step();
        }
    }
    pub fn run_n_steps(&mut self, steps: u32) {
        for _ in 0..steps {
            self.step();
        }
    }

    fn step(&mut self) {
        while self.pc < self.program.len() {
            let instr = Instr::decode(&self.program[self.pc..]);
            self.pc += instr.size();
            match instr {
                Instr::PushInt(n) => {
                    println!("pushing int");
                    self.push(n);
                }
                Instr::PushBool(b) => {
                    self.push(b);
                }
                Instr::Pop => {
                    self.value_stack.pop();
                }
                Instr::Add => {
                    let b = self.pop_int();
                    let a = self.pop_int();
                    self.push(a + b);
                }
                Instr::Sub => {
                    println!("subtracting");
                    let b = self.pop_int();
                    let a = self.pop_int();
                    self.push(a - b);
                }
                Instr::Mul => {
                    let b = self.pop_int();
                    let a = self.pop_int();
                    self.push(a * b);
                }
                Instr::Div => {
                    let b = self.pop_int();
                    let a = self.pop_int();
                    self.push(a / b);
                }
                Instr::Jump(target) => {
                    self.pc = target;
                    continue;
                }
                Instr::JumpIfTrue(target) => {
                    let v = self.pop_bool();
                    if v {
                        self.pc = target;
                        continue;
                    }
                }
                Instr::Call(target) => {
                    self.call_stack.push(CallFrame {
                        pc: self.pc + 1,
                        stack_base: self.value_stack.len(),
                    });
                    self.pc = target;
                    continue;
                }
                Instr::Return => {
                    let frame = self.call_stack.pop().expect("call stack underflow");
                    self.pc = frame.pc;
                    self.value_stack.truncate(frame.stack_base);
                }
            }
        }
    }

    pub(crate) fn compact(&mut self) {
        self.value_stack.shrink_to_fit();
        self.call_stack.shrink_to_fit();
    }

    pub(crate) fn gc(&mut self) {
        // TODO
    }

    fn push(&mut self, x: impl Into<Value>) {
        self.value_stack.push(x.into());
    }

    fn pop_int(&mut self) -> i64 {
        self.value_stack.pop().expect("stack underflow").get_int()
    }

    fn pop_bool(&mut self) -> bool {
        self.value_stack.pop().expect("stack underflow").get_bool()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic() {
        let program_str = r#"
pushi 3
pushi 4
sub
"#;
        let program_bytes = assemble(program_str);
        let mut vm = Vm::new(program_bytes);
        vm.run();
        assert_eq!(vm.top().get_int(), -1);
    }
}
