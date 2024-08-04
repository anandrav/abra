type ProgramCounter = usize;

#[derive(Debug)]
pub struct Vm {
    program: Vec<Instr>,
    pc: ProgramCounter,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    heap: Vec<HeapObject>,
}

#[derive(Debug, Copy, Clone)]
enum Instr {
    Push(Value),
    Pop,
    Add,
    Sub,
    Mul,
    Div,

    Jump(ProgramCounter),
    JumpIfTrue(ProgramCounter),
    Call(ProgramCounter),

    CompareInt,
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
struct HeapObject {
    // mark: bool,
    kind: HeapObjectKind,
}

#[derive(Debug)]
enum HeapObjectKind {
    Record(Vec<Value>),
    String(String),
    DynArray(Vec<Value>),
    FunctionObject {
        closure: (), /* TODO */
        addr: ProgramCounter,
    },
}

impl Vm {
    pub fn run(&mut self, steps: u32) {
        for _ in 0..steps {
            while let Some(instr) = self.program.get(self.pc).cloned() {
                match instr {
                    Instr::Push(value) => {
                        self.value_stack.push(value);
                    }
                    Instr::Pop => {
                        self.value_stack.pop();
                    }
                    Instr::Add => {
                        let a = self.pop_int();
                        let b = self.pop_int();
                        self.push(a + b);
                    }
                    Instr::Sub => {
                        let a = self.pop_int();
                        let b = self.pop_int();
                        self.push(a - b);
                    }
                    Instr::Mul => {
                        let a = self.pop_int();
                        let b = self.pop_int();
                        self.push(a * b);
                    }
                    Instr::Div => {
                        let a = self.pop_int();
                        let b = self.pop_int();
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
                    Instr::CompareInt => {
                        let a = self.pop_int();
                        let b = self.pop_int();
                        let result: i64 = match a.cmp(&b) {
                            std::cmp::Ordering::Greater => 1,
                            std::cmp::Ordering::Less => -1,
                            std::cmp::Ordering::Equal => 0,
                        };
                        self.push(result);
                    }
                }
                self.pc += 1;
            }
        }
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
