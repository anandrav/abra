type ProgramCounter = usize;
pub type AbraInt = i64;
use core::fmt;
use std::fmt::{Display, Formatter};

use crate::assembly::assemble;

#[derive(Debug)]
pub struct Vm {
    program: Vec<Instr>,
    pc: ProgramCounter,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    heap: Vec<ManagedObject>,
}

impl Vm {
    pub fn new(program: Vec<Instr>) -> Self {
        Self {
            program,
            pc: 0,
            value_stack: Vec::new(),
            call_stack: Vec::new(),
            heap: Vec::new(),
        }
    }

    pub fn top(&self) -> &Value {
        self.value_stack.last().expect("stack underflow")
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Instr {
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
}

impl From<Opcode> for String {
    fn from(opcode: Opcode) -> String {
        match opcode {
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

impl Display for Opcode {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        write!(f, "{}", String::from(*self))
    }
}

// impl Instr {
//     pub(crate) fn opcode(&self) -> Opcode {
//         match self {
//             Instr::Pop => Opcode::Pop,
//             Instr::Add => Opcode::Add,
//             Instr::Sub => Opcode::Sub,
//             Instr::Mul => Opcode::Mul,
//             Instr::Div => Opcode::Div,
//             Instr::Return => Opcode::Return,
//             Instr::PushBool(_) => Opcode::PushBool,
//             Instr::PushInt(_) => Opcode::PushInt,
//             Instr::Jump(_) => Opcode::Jump,
//             Instr::JumpIfTrue(_) => Opcode::JumpIfTrue,
//             Instr::Call(_) => Opcode::Call,
//         }
//     }
// }

impl Into<String> for &Instr {
    fn into(self) -> String {
        match self {
            Instr::Pop => "pop".to_owned(),
            Instr::Add => "add".to_owned(),
            Instr::Sub => "sub".to_owned(),
            Instr::Mul => "mul".to_owned(),
            Instr::Div => "div".to_owned(),
            Instr::Return => "ret".to_owned(),
            Instr::PushBool(b) => format!("pushb {}", b),
            Instr::PushInt(n) => format!("pushi {}", n),
            Instr::Jump(loc) => format!("jump {}", loc),
            Instr::JumpIfTrue(loc) => format!("jumpif {}", loc),
            Instr::Call(loc) => format!("call {}", loc),
        }
    }
}

impl Display for Instr {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        let s: String = self.into();
        write!(f, "{}", s)
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Value {
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
    pub fn get_int(&self) -> AbraInt {
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
        captured_values: Vec<Value>, /* TODO */
        func_addr: ProgramCounter,
    },
}

impl Vm {
    pub fn run(&mut self) {
        println!("pc is {}, len is {}", self.pc, self.program.len());
        while self.pc < self.program.len() {
            self.step();
            println!("step done");
        }
        println!("done running vm");
    }
    pub fn run_n_steps(&mut self, steps: u32) {
        for _ in 0..steps {
            self.step();
        }
    }

    fn step(&mut self) {
        while self.pc < self.program.len() {
            let instr = self.program[self.pc];
            self.pc += 1;
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
                    println!("adding");
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
        let instructions = assemble(program_str);
        let mut vm = Vm::new(instructions);
        vm.run();
        assert_eq!(vm.top().get_int(), -1);
    }

    #[test]
    fn arithmetic2() {
        let program_str = r#"
pushi 2
pushi 3
add
pushi 1
sub
"#;
        let instructions = assemble(program_str);
        let mut vm = Vm::new(instructions);
        vm.run();
        assert_eq!(vm.top().get_int(), 4);
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
        let instructions = assemble(program_str);
        let mut vm = Vm::new(instructions);
        vm.run();
        assert_eq!(vm.top().get_int(), 7);
    }
}
