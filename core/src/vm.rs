type ProgramCounter = usize;
pub type AbraInt = i64;
use crate::assembly::assemble;
use core::fmt;
use std::fmt::{Display, Formatter};

pub struct Vm {
    program: Vec<Instr>,
    pc: ProgramCounter,
    stack_base: usize,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    heap: Vec<ManagedObject>,

    string_table: Vec<String>,
    pending_effect: Option<u16>,
}

impl Vm {
    pub fn new(program: Vec<Instr>, string_table: Vec<String>) -> Self {
        Self {
            program,
            pc: 0,
            stack_base: 0,
            value_stack: Vec::new(),
            call_stack: Vec::new(),
            heap: Vec::new(),

            string_table,
            pending_effect: None,
        }
    }

    pub fn top(&self) -> &Value {
        self.value_stack.last().expect("stack underflow")
    }

    pub fn pop(&mut self) -> Value {
        self.value_stack.pop().expect("stack underflow")
    }

    pub fn push_str(&mut self, s: &str) {
        self.heap.push(ManagedObject {
            kind: ManagedObjectKind::String(s.to_owned()),
        });
        self.push(Value::ManagedObject(self.heap.len()));
    }

    pub fn push_nil(&mut self) {
        self.push(Value::Nil);
    }

    pub fn get_pending_effect(&self) -> Option<u16> {
        self.pending_effect
    }

    pub fn clear_pending_effect(&mut self) {
        self.pending_effect = None;
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Instr<Location = ProgramCounter, StringConstant = u16> {
    Pop,
    LoadOffset(i32),
    StoreOffset(i32),
    Add,
    Sub,
    Mul,
    Div,
    Not,
    Return,
    Stop,
    PushNil,
    PushBool(bool),
    PushInt(AbraInt),
    PushString(StringConstant),
    Jump(Location),
    JumpIf(Location),
    Call(Location, u8),
    Construct(u8),
    Unpack,
    Effect(u16),
}

impl From<&Instr> for String {
    fn from(val: &Instr) -> Self {
        match val {
            Instr::Pop => "pop".to_owned(),
            Instr::LoadOffset(n) => format!("loadoffset {}", n),
            Instr::StoreOffset(n) => format!("storeoffset {}", n),
            Instr::Add => "add".to_owned(),
            Instr::Sub => "sub".to_owned(),
            Instr::Mul => "mul".to_owned(),
            Instr::Div => "div".to_owned(),
            Instr::Not => "not".to_owned(),
            Instr::Return => "return".to_owned(),
            Instr::Stop => "stop".to_owned(),
            Instr::PushNil => "pushnil".to_owned(),
            Instr::PushBool(b) => format!("pushbool {}", b),
            Instr::PushInt(n) => format!("pushint {}", n),
            Instr::PushString(s) => format!("pushstring \"{}\"", s),
            Instr::Jump(loc) => format!("jump {}", loc),
            Instr::JumpIf(loc) => format!("jumpif {}", loc),
            Instr::Call(loc, nargs) => format!("call {} {}", loc, nargs),
            Instr::Construct(n) => format!("construct {}", n),
            Instr::Unpack => "unpack".to_owned(),
            Instr::Effect(n) => format!("effect {}", n),
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
    Nil,
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

    pub fn get_bool(&self) -> bool {
        match self {
            Value::Bool(b) => *b,
            _ => panic!("not a bool"),
        }
    }

    pub fn get_string(&self, vm: &Vm) -> String {
        match self {
            Value::ManagedObject(idx) => match &vm.heap[*idx - 1].kind {
                ManagedObjectKind::String(s) => s.clone(),
                _ => panic!("not a string"),
            },
            _ => panic!("not a string"),
        }
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_top: usize,
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
        if self.pending_effect.is_some() {
            panic!("must handle pending effect");
        }
        println!("pc is {}, len is {}", self.pc, self.program.len());
        while self.pc < self.program.len() && self.pending_effect.is_none() {
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
        dbg!(&self);
        let instr = self.program[self.pc];
        println!("{:?}", instr);
        self.pc += 1;
        match instr {
            Instr::PushNil => {
                self.push(Value::Nil);
            }
            Instr::PushInt(n) => {
                println!("pushing int");
                self.push(n);
            }
            Instr::PushBool(b) => {
                self.push(b);
            }
            Instr::PushString(idx) => {
                let s = &self.string_table[idx as usize];
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::String(s.clone()),
                });
                self.push(Value::ManagedObject(self.heap.len()));
            }
            Instr::Pop => {
                self.value_stack.pop();
            }
            Instr::LoadOffset(n) => {
                let idx = self.stack_base.wrapping_add_signed(n as isize);
                let v = self.value_stack[idx];
                self.push(v);
            }
            Instr::StoreOffset(n) => {
                let idx = self.stack_base.wrapping_add_signed(n as isize);
                let v = self.value_stack.pop().expect("stack underflow");
                self.value_stack[idx] = v;
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
            Instr::Not => {
                let v = self.pop_bool();
                self.push(!v);
            }
            Instr::Jump(target) => {
                self.pc = target;
            }
            Instr::JumpIf(target) => {
                let v = self.pop_bool();
                if v {
                    self.pc = target;
                }
            }
            Instr::Call(target, nargs) => {
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_top: self.value_stack.len() - nargs as usize,
                });
                self.pc = target;
                self.stack_base = self.value_stack.len();
            }
            Instr::Return => {
                let ret_value = self.value_stack.pop().expect("stack underflow");
                let frame = self.call_stack.pop().expect("call stack underflow");
                self.pc = frame.pc;
                self.stack_base = self.call_stack.last().map(|f| f.stack_top).unwrap_or(0);
                self.value_stack.truncate(frame.stack_top);
                self.value_stack.push(ret_value);
            }
            Instr::Stop => {
                self.pc = self.program.len();
                return;
            }
            Instr::Construct(n) => {
                let fields = self
                    .value_stack
                    .split_off(self.value_stack.len() - n as usize);
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::Record(fields),
                });
                self.value_stack.push(Value::ManagedObject(self.heap.len()));
            }
            Instr::Unpack => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let fields = match &obj {
                    Value::ManagedObject(idx) => match &self.heap[*idx - 1].kind {
                        ManagedObjectKind::Record(fields) => fields.clone(),
                        _ => panic!("not a tuple"),
                    },
                    _ => panic!("not a tuple"),
                };
                self.value_stack.extend(fields);
            }
            Instr::Effect(eff) => {
                self.pending_effect = Some(eff);
            }
        }
        dbg!(&self);
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

impl fmt::Debug for Vm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Vm")
            .field("pc", &self.pc)
            .field("stack_base", &self.stack_base)
            .field("value_stack", &format!("{:?}", self.value_stack))
            .field("call_stack", &format!("{:?}", self.call_stack))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic() {
        let program_str = r#"
pushint 3
pushint 4
sub
"#;
        let (instructions, string_table) = assemble(program_str);
        let mut vm = Vm::new(instructions, string_table);
        vm.run();
        assert_eq!(vm.top().get_int(), -1);
    }

    #[test]
    fn arithmetic2() {
        let program_str = r#"
pushint 2
pushint 3
add
pushint 1
sub
"#;
        let (instructions, string_table) = assemble(program_str);
        let mut vm = Vm::new(instructions, string_table);
        vm.run();
        assert_eq!(vm.top().get_int(), 4);
    }

    #[test]
    fn jump_to_label() {
        let program_str = r#"
pushint 3
pushint 4
jump my_label
pushint 100
my_label:
add
"#;
        let (instructions, string_table) = assemble(program_str);
        let mut vm = Vm::new(instructions, string_table);
        vm.run();
        assert_eq!(vm.top().get_int(), 7);
    }
}
