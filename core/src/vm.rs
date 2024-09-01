type ProgramCounter = usize;
pub type AbraInt = i64;
pub type AbraFloat = f64;
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

    pub fn push_int(&mut self, n: AbraInt) {
        self.push(Value::Int(n));
    }

    pub fn push_str(&mut self, s: &str) {
        self.heap.push(ManagedObject {
            kind: ManagedObjectKind::String(s.to_owned()),
        });
        self.push(Value::ManagedObject(self.heap.len() - 1));
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

    pub fn is_done(&self) -> bool {
        self.pc >= self.program.len()
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Instr<Location = ProgramCounter, StringConstant = u16> {
    // Stack manipulation
    Pop,
    Duplicate,
    LoadOffset(i32),
    StoreOffset(i32),

    // Constants
    PushNil,
    PushBool(bool),
    PushInt(AbraInt),
    PushFloat(AbraFloat),
    PushString(StringConstant),

    // TODO: Once monomorphization is implemented, create separate operators for int and float

    // Arithmetic
    Add,
    Subtract,
    Multiply,
    Divide,
    SquareRoot,
    Power,

    // Logical
    Not,
    And,
    Or,

    // Comparison
    LessThan,
    LessThanOrEqual,
    GreaterThan,
    GreaterThanOrEqual,
    Equal,

    // Control Flow
    Jump(Location),
    JumpIf(Location),
    Call(Location),
    CallFuncObj,
    Return,

    // Data Structures
    Construct(u16),
    Deconstruct,
    GetField(u16),
    SetField(u16),
    GetIdx,
    SetIdx,
    ConstructVariant {
        tag: u16,
    },
    MakeClosure {
        n_captured: u16,
        func_addr: Location,
    },

    ArrayAppend,
    ArrayLen,
    ArrayPop,
    ConcatStrings,
    IntToString,
    FloatToString,

    // Effects
    Stop,
    Effect(u16),
}

impl<L: Display, S: Display> Display for Instr<L, S> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        match self {
            Instr::Pop => write!(f, "pop"),
            Instr::Duplicate => write!(f, "duplicate"),
            Instr::LoadOffset(n) => write!(f, "loadOffset {}", n),
            Instr::StoreOffset(n) => write!(f, "storeOffset {}", n),
            Instr::Add => write!(f, "add"),
            Instr::Subtract => write!(f, "subtract"),
            Instr::Multiply => write!(f, "multiply"),
            Instr::Divide => write!(f, "divide"),
            Instr::SquareRoot => write!(f, "square_root"),
            Instr::Power => write!(f, "power"),
            Instr::Not => write!(f, "not"),
            Instr::And => write!(f, "and"),
            Instr::Or => write!(f, "or"),
            Instr::LessThan => write!(f, "less_than"),
            Instr::LessThanOrEqual => write!(f, "less_than_or_equal"),
            Instr::GreaterThan => write!(f, "greater_than"),
            Instr::GreaterThanOrEqual => write!(f, "greater_than_or_equal"),
            Instr::Equal => write!(f, "equal"),
            Instr::PushNil => write!(f, "push_nil"),
            Instr::PushBool(b) => write!(f, "push_bool {}", b),
            Instr::PushInt(n) => write!(f, "push_int {}", n),
            Instr::PushFloat(n) => write!(f, "push_float {}", n),
            Instr::PushString(s) => write!(f, "push_string \"{}\"", s),
            Instr::Jump(loc) => write!(f, "jump {}", loc),
            Instr::JumpIf(loc) => write!(f, "jump_if {}", loc),
            Instr::Call(loc) => write!(f, "call {}", loc),
            Instr::CallFuncObj => write!(f, "call_func_obj"),
            Instr::Return => write!(f, "return"),
            Instr::Construct(n) => write!(f, "construct {}", n),
            Instr::Deconstruct => write!(f, "deconstruct"),
            Instr::GetField(n) => write!(f, "get_field {}", n),
            Instr::SetField(n) => write!(f, "set_field {}", n),
            Instr::GetIdx => write!(f, "get_index"),
            Instr::SetIdx => write!(f, "set_index"),
            Instr::ConstructVariant { tag } => {
                write!(f, "construct_variant {}", tag)
            }
            Instr::MakeClosure {
                n_captured,
                func_addr,
            } => {
                write!(f, "make_closure {} {}", n_captured, func_addr)
            }
            Instr::ArrayAppend => write!(f, "array_append"),
            Instr::ArrayLen => write!(f, "array_len"),
            Instr::ArrayPop => write!(f, "array_pop"),
            Instr::ConcatStrings => write!(f, "concat_strings"),
            Instr::IntToString => write!(f, "int_to_string"),
            Instr::FloatToString => write!(f, "float_to_string"),
            Instr::Stop => write!(f, "stop"),
            Instr::Effect(n) => write!(f, "effect {}", n),
        }
    }
}

#[derive(Debug, Copy, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(AbraInt),
    Float(AbraFloat),
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

impl From<AbraFloat> for Value {
    fn from(n: AbraFloat) -> Value {
        Value::Float(n)
    }
}

impl Value {
    pub fn get_int(&self) -> AbraInt {
        match self {
            Value::Int(n) => *n,
            _ => panic!("not an int"),
        }
    }

    pub fn get_float(&self) -> AbraFloat {
        match self {
            Value::Float(f) => *f,
            _ => panic!("not a float"),
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
            Value::ManagedObject(idx) => match &vm.heap[*idx].kind {
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
        tag: u16,
        value: Value,
    },
    // DynArray is also used for tuples and structs
    DynArray(Vec<Value>),
    String(String),
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
        // dbg!(&self);
        while !self.is_done() && self.pending_effect.is_none() {
            self.step();
            // dbg!(&self);
        }

        if self.is_done() {
            // println!("DONE");
        }
    }

    pub fn run_n_steps(&mut self, steps: u32) {
        for _ in 0..steps {
            self.step();
        }
    }

    fn step(&mut self) {
        let instr = self.program[self.pc];
        // println!("Instruction: {:?}", instr);
        self.pc += 1;
        match instr {
            Instr::PushNil => {
                self.push(Value::Nil);
            }
            Instr::PushInt(n) => {
                self.push(n);
            }
            Instr::PushFloat(f) => {
                self.push(f);
            }
            Instr::PushBool(b) => {
                self.push(b);
            }
            Instr::PushString(idx) => {
                let s = &self.string_table[idx as usize];
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::String(s.clone()),
                });
                self.push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::Pop => {
                self.value_stack.pop();
            }
            Instr::Duplicate => {
                let v = self.top();
                self.push(*v);
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
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a + b),
                    (Value::Float(a), Value::Float(b)) => self.push(a + b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Subtract => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a - b),
                    (Value::Float(a), Value::Float(b)) => self.push(a - b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Multiply => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a * b),
                    (Value::Float(a), Value::Float(b)) => self.push(a * b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Divide => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a / b),
                    (Value::Float(a), Value::Float(b)) => self.push(a / b),
                    _ => panic!("not a number"),
                }
            }
            Instr::SquareRoot => {
                let v = self.pop();
                match v {
                    Value::Float(f) => self.push(f.sqrt()),
                    _ => panic!("not a float"),
                }
            }
            Instr::Power => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a.pow(b as u32)),
                    (Value::Float(a), Value::Float(b)) => self.push(a.powf(b)),
                    _ => panic!("not a number"),
                }
            }
            Instr::Not => {
                let v = self.pop_bool();
                self.push(!v);
            }
            Instr::And => {
                let b = self.pop_bool();
                let a = self.pop_bool();
                self.push(a && b);
            }
            Instr::Or => {
                let b = self.pop_bool();
                let a = self.pop_bool();
                self.push(a || b);
            }
            Instr::LessThan => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a < b),
                    (Value::Float(a), Value::Float(b)) => self.push(a < b),
                    _ => panic!("not a number"),
                }
            }
            Instr::LessThanOrEqual => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a <= b),
                    (Value::Float(a), Value::Float(b)) => self.push(a <= b),
                    _ => panic!("not a number"),
                }
            }
            Instr::GreaterThan => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a > b),
                    (Value::Float(a), Value::Float(b)) => self.push(a > b),
                    _ => panic!("not a number"),
                }
            }
            Instr::GreaterThanOrEqual => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a >= b),
                    (Value::Float(a), Value::Float(b)) => self.push(a >= b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Equal => {
                let b = self.pop();
                let a = self.pop();
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a == b),
                    (Value::Float(a), Value::Float(b)) => self.push(a == b),
                    (Value::Bool(a), Value::Bool(b)) => self.push(a == b),
                    (Value::Nil, Value::Nil) => self.push(true),
                    _ => self.push(false),
                }
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
            Instr::Call(target) => {
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_base: self.stack_base,
                });
                self.pc = target;
                self.stack_base = self.value_stack.len();
            }
            Instr::CallFuncObj => {
                let func_obj = self.value_stack.pop().expect("stack underflow");
                match &func_obj {
                    Value::ManagedObject(id) => match &self.heap[*id].kind {
                        ManagedObjectKind::FunctionObject {
                            captured_values,
                            func_addr,
                        } => {
                            self.call_stack.push(CallFrame {
                                pc: self.pc,
                                stack_base: self.stack_base,
                            });
                            self.pc = *func_addr;
                            self.stack_base = self.value_stack.len();
                            self.value_stack.extend(captured_values.iter().cloned());
                        }
                        _ => panic!("not a function object"),
                    },
                    _ => panic!("not a function object"),
                }
            }
            Instr::Return => {
                let frame = self.call_stack.pop().expect("call stack underflow");
                self.pc = frame.pc;
                self.stack_base = frame.stack_base;
            }
            Instr::Stop => self.pc = self.program.len(),
            Instr::Construct(n) => {
                let fields = self
                    .value_stack
                    .split_off(self.value_stack.len() - n as usize);
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::DynArray(fields),
                });
                self.value_stack
                    .push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::Deconstruct => {
                let obj = self.value_stack.pop().expect("stack underflow");
                match &obj {
                    Value::ManagedObject(idx) => match &self.heap[*idx].kind {
                        ManagedObjectKind::DynArray(fields) => {
                            self.value_stack.extend(fields.iter().rev());
                        }
                        ManagedObjectKind::Adt { tag, value } => {
                            self.value_stack.push(*value);
                            self.push_int(*tag as AbraInt);
                        }
                        _ => panic!("not a tuple"),
                    },
                    _ => panic!("not a tuple"),
                };
            }
            Instr::GetField(index) => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let field = match &obj {
                    Value::ManagedObject(id) => match &self.heap[*id].kind {
                        ManagedObjectKind::DynArray(fields) => fields[index as usize],
                        _ => panic!("not a tuple"),
                    },
                    _ => panic!("not a tuple"),
                };
                self.push(field);
            }
            Instr::SetField(index) => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let rvalue = self.value_stack.pop().expect("stack underflow");
                let obj_id = match &obj {
                    Value::ManagedObject(id) => *id,
                    _ => panic!("not a managed object: {:?}", obj),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        fields[index as usize] = rvalue;
                    }
                    _ => panic!("not a record type: {:?}", self.heap[obj_id]),
                }
            }
            Instr::GetIdx => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let idx = self.pop_int();
                let field = match &obj {
                    Value::ManagedObject(id) => match &self.heap[*id].kind {
                        ManagedObjectKind::DynArray(fields) => fields[idx as usize],
                        _ => panic!("not a dynamic array"),
                    },
                    _ => panic!("not a dynamic array"),
                };
                self.push(field);
            }
            Instr::SetIdx => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let idx = self.pop_int();
                let rvalue = self.value_stack.pop().expect("stack underflow");
                let obj_id = match &obj {
                    Value::ManagedObject(id) => *id,
                    _ => panic!("not a managed object: {:?}", obj),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        fields[idx as usize] = rvalue;
                    }
                    _ => panic!("not a dynamic array: {:?}", self.heap[obj_id]),
                }
            }
            Instr::ConstructVariant { tag } => {
                let value = self.pop();
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::Adt { tag, value },
                });
                self.value_stack
                    .push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::MakeClosure {
                n_captured,
                func_addr,
            } => {
                let captured_values = self
                    .value_stack
                    .split_off(self.value_stack.len() - n_captured as usize);
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::FunctionObject {
                        captured_values,
                        func_addr,
                    },
                });
                self.value_stack
                    .push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::ArrayAppend => {
                let rvalue = self.pop();
                let obj = self.value_stack.pop().expect("stack underflow");
                let obj_id = match &obj {
                    Value::ManagedObject(id) => *id,
                    _ => panic!("not a managed object: {:?}", obj),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        fields.push(rvalue);
                    }
                    _ => panic!("not a dynamic array: {:?}", self.heap[obj_id]),
                }
                self.push_nil();
            }
            Instr::ArrayLen => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let len = match &obj {
                    Value::ManagedObject(id) => match &self.heap[*id].kind {
                        ManagedObjectKind::DynArray(fields) => fields.len(),
                        _ => panic!("not a dynamic array"),
                    },
                    _ => panic!("not a dynamic array"),
                };
                self.push_int(len as AbraInt);
            }
            Instr::ArrayPop => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let obj_id = match &obj {
                    Value::ManagedObject(id) => *id,
                    _ => panic!("not a managed object: {:?}", obj),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        let rvalue = fields.pop().expect("array underflow");
                        self.push(rvalue);
                    }
                    _ => panic!("not a dynamic array: {:?}", self.heap[obj_id]),
                }
            }
            Instr::ConcatStrings => {
                let b = self.pop();
                let a = self.pop();
                let a_str = a.get_string(self);
                let b_str = b.get_string(self);
                let result = a_str + &b_str;
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::String(result),
                });
                self.push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::IntToString => {
                let n = self.pop_int();
                let s = n.to_string();
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::String(s),
                });
                self.push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::FloatToString => {
                let f = self.pop().get_float();
                let s = f.to_string();
                self.heap.push(ManagedObject {
                    kind: ManagedObjectKind::String(s),
                });
                self.push(Value::ManagedObject(self.heap.len() - 1));
            }
            Instr::Effect(eff) => {
                self.pending_effect = Some(eff);
            }
        }
    }

    pub(crate) fn _compact(&mut self) {
        self.value_stack.shrink_to_fit();
        self.call_stack.shrink_to_fit();
    }

    pub(crate) fn _gc(&mut self) {
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
            .field("heap", &format!("{:?}", self.heap))
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::assembly::_assemble;

    #[test]
    fn arithmetic() {
        let program_str = r#"
push_int 3
push_int 4
subtract
"#;
        let (instructions, string_table) = _assemble(program_str);
        let mut vm = Vm::new(instructions, string_table);
        vm.run();
        assert_eq!(vm.top().get_int(), -1);
    }

    #[test]
    fn arithmetic2() {
        let program_str = r#"
push_int 2
push_int 3
add
push_int 1
subtract
"#;
        let (instructions, string_table) = _assemble(program_str);
        let mut vm = Vm::new(instructions, string_table);
        vm.run();
        assert_eq!(vm.top().get_int(), 4);
    }

    #[test]
    fn jump_to_label() {
        let program_str = r#"
push_int 3
push_int 4
jump my_label
push_int 100
my_label:
add
"#;
        let (instructions, string_table) = _assemble(program_str);
        let mut vm = Vm::new(instructions, string_table);
        vm.run();
        assert_eq!(vm.top().get_int(), 7);
    }
}
