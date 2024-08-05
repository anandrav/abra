type ProgramCounter = usize;
type AbraInt = i64;
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
    PushInt(AbraInt),
    Jump(ProgramCounter),
    JumpIfTrue(ProgramCounter),
    Call(ProgramCounter),
}

#[derive(Debug, Copy, Clone)]
#[repr(u8)]
pub(crate) enum Opcode {
    Pop,
    Add,
    Sub,
    Mul,
    Div,
    Return,
    PushBool,
    PushInt,
    Jump,
    JumpIfTrue,
    Call,
}

impl Opcode {
    pub(crate) fn nbytes(&self) -> usize {
        match self {
            Opcode::Pop
            | Opcode::Add
            | Opcode::Sub
            | Opcode::Mul
            | Opcode::Div
            | Opcode::Return => 1,
            Opcode::PushBool => 2,
            Opcode::PushInt => 1 + size_of::<AbraInt>(),
            Opcode::Jump | Opcode::JumpIfTrue | Opcode::Call => 1 + size_of::<ProgramCounter>(),
        }
    }

    pub(crate) fn from_str(s: &str) -> Option<Opcode> {
        match s {
            "pop" => Some(Opcode::Pop),
            "add" => Some(Opcode::Add),
            "sub" => Some(Opcode::Sub),
            "mul" => Some(Opcode::Mul),
            "div" => Some(Opcode::Div),
            "ret" => Some(Opcode::Return),
            "pushb" => Some(Opcode::PushBool),
            "pushi" => Some(Opcode::PushInt),
            "jump" => Some(Opcode::Jump),
            "jumpif" => Some(Opcode::JumpIfTrue),
            "call" => Some(Opcode::Call),
            _ => None,
        }
    }

    pub(crate) fn to_string(&self) -> String {
        match self {
            Opcode::Pop => "pop".into(),
            Opcode::Add => "add".into(),
            Opcode::Sub => "sub".into(),
            Opcode::Mul => "mul".into(),
            Opcode::Div => "div".into(),
            Opcode::Return => "ret".into(),
            Opcode::PushBool => "pushb".into(),
            Opcode::PushInt => "pushi".into(),
            Opcode::Jump => "jump".into(),
            Opcode::JumpIfTrue => "jumpif".into(),
            Opcode::Call => "call".into(),
        }
    }
}

impl Instr {
    pub(crate) fn opcode(&self) -> Opcode {
        match self {
            Instr::Pop => Opcode::Pop,
            Instr::Add => Opcode::Add,
            Instr::Sub => Opcode::Sub,
            Instr::Mul => Opcode::Mul,
            Instr::Div => Opcode::Div,
            Instr::Return => Opcode::Return,
            Instr::PushBool(_) => Opcode::PushBool,
            Instr::PushInt(_) => Opcode::PushInt,
            Instr::Jump(_) => Opcode::Jump,
            Instr::JumpIfTrue(_) => Opcode::JumpIfTrue,
            Instr::Call(_) => Opcode::Call,
        }
    }

    pub(crate) fn size(&self) -> usize {
        let mut n = 1;
        match self {
            Instr::Pop | Instr::Add | Instr::Sub | Instr::Mul | Instr::Div | Instr::Return => {}
            Instr::PushBool(_) => n += size_of::<bool>(),
            Instr::PushInt(_) => n += size_of::<AbraInt>(),
            Instr::Jump(_) | Instr::JumpIfTrue(_) | Instr::Call(_) => n += size_of::<usize>(),
        }
        n
    }

    pub(crate) fn encode(&self, buf: &mut Vec<u8>) {
        buf.push(self.opcode() as u8);
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
            7 => Instr::PushInt(AbraInt::from_le_bytes(buf[1..9].try_into().unwrap())),
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
    Int(AbraInt),
    ManagedObject(usize),
}

impl From<bool> for Value {
    fn from(b: bool) -> Value {
        Value::Bool(b)
    }
}

impl From<AbraInt> for Value {
    fn from(n: AbraInt) -> Value {
        Value::Int(n)
    }
}

impl Value {
    fn get_int(&self) -> AbraInt {
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

    fn pop_int(&mut self) -> AbraInt {
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
        let bytecode = assemble(program_str);
        let mut vm = Vm::new(bytecode);
        vm.run();
        assert_eq!(vm.top().get_int(), -1);
    }

    #[test]
    fn jump_to_label() {
        let program_str = r#"
pushi 3
pushi 4
jump my_label
pushi 100
my_label:
add
"#;
        let bytecode = assemble(program_str);
        let mut vm = Vm::new(bytecode);
        vm.run();
        assert_eq!(vm.top().get_int(), 7);
    }
}
