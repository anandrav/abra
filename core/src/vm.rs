type ProgramCounter = usize;
pub type AbraInt = i64;
pub type AbraFloat = f64;

#[cfg(feature = "ffi")]
use libloading::Library;

use crate::translate_bytecode::{BytecodeIndex, CompiledProgram};
use core::fmt;
use std::error::Error;
use std::fmt::Debug;
use std::{
    cell::Cell,
    fmt::{Display, Formatter},
    mem,
};

type Result<T> = std::result::Result<T, VmError>;

#[repr(C)]
pub struct Vm {
    program: Vec<Instr>,
    pc: ProgramCounter,
    stack_base: usize,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    heap: Vec<ManagedObject>,
    heap_group: HeapGroup,

    static_strings: Vec<String>,
    filename_arena: Vec<String>,
    function_name_arena: Vec<String>,

    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,

    pending_effect: Option<u16>,
    error: Option<VmError>,

    // FFI
    #[cfg(feature = "ffi")]
    libs: Vec<Library>,
    #[cfg(feature = "ffi")]
    foreign_functions: Vec<unsafe extern "C" fn(*mut Vm) -> ()>,
}

pub enum VmStatus {
    Done,
    PendingEffect(u16),
    OutOfSteps,
    Error(VmError),
}

#[derive(Clone, Debug)]
pub struct VmError {
    kind: VmErrorKind,
    location: VmErrorLocation,
    trace: Vec<VmErrorLocation>,
}

#[derive(Clone, Debug)]
pub struct VmErrorLocation {
    filename: String,
    lineno: u32,
    function_name: String,
}

#[derive(Clone, Debug)]
pub enum VmErrorKind {
    ArrayOutOfBounds,
    Panic(String),
    Underflow,
    WrongType,
}

pub type ErrorLocation = (String, u32);

impl Vm {
    pub fn new(program: CompiledProgram) -> Self {
        Self {
            program: program.instructions,
            pc: 0,
            stack_base: 0,
            value_stack: Vec::new(),
            call_stack: Vec::new(),
            heap: Vec::new(),
            heap_group: HeapGroup::One,

            static_strings: program.static_strings,
            filename_arena: program.filename_arena,
            function_name_arena: program.function_name_arena,

            filename_table: program.filename_table,
            lineno_table: program.lineno_table,
            function_name_table: program.function_name_table,

            pending_effect: None,
            error: None,

            #[cfg(feature = "ffi")]
            libs: Vec::new(),
            #[cfg(feature = "ffi")]
            foreign_functions: Vec::new(),
        }
    }

    pub fn with_entry_point(program: CompiledProgram, entry_point: String) -> Self {
        Self {
            program: program.instructions,
            pc: program.label_map[&entry_point],
            stack_base: 0,
            value_stack: Vec::new(),
            call_stack: Vec::new(),
            heap: Vec::new(),
            heap_group: HeapGroup::One,

            static_strings: program.static_strings,
            filename_arena: program.filename_arena,
            function_name_arena: program.function_name_arena,

            filename_table: program.filename_table,
            lineno_table: program.lineno_table,
            function_name_table: program.function_name_table,

            pending_effect: None,
            error: None,

            #[cfg(feature = "ffi")]
            libs: Vec::new(),
            #[cfg(feature = "ffi")]
            foreign_functions: Vec::new(),
        }
    }

    pub fn status(&self) -> VmStatus {
        if self.pending_effect.is_some() {
            VmStatus::PendingEffect(self.pending_effect.unwrap())
        } else if self.is_done() {
            VmStatus::Done
        } else if let Some(err) = &self.error {
            VmStatus::Error(err.clone())
        } else {
            VmStatus::OutOfSteps
        }
    }

    pub fn top(&self) -> &Value {
        self.value_stack.last().expect("stack underflow")
    }

    pub fn pop(&mut self) -> Result<Value> {
        match self.value_stack.pop() {
            Some(v) => Ok(v),
            None => Err(self.make_error(VmErrorKind::Underflow)),
        }
    }

    pub fn push_int(&mut self, n: AbraInt) {
        self.push(n);
    }

    pub fn push_str(&mut self, s: String) {
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::String(s)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    pub fn push_nil(&mut self) {
        self.push(Value::Nil);
    }

    pub fn push_bool(&mut self, b: bool) {
        self.push(b);
    }

    pub fn push_float(&mut self, f: AbraFloat) {
        self.push(f);
    }

    pub fn construct_tuple(&mut self, n: u16) {
        let fields = self
            .value_stack
            .split_off(self.value_stack.len() - n as usize);
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::DynArray(fields)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    pub fn construct_variant(&mut self, tag: u16) -> Result<()> {
        let value = self.pop()?;
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::Enum { tag, value }));
        let r = self.heap_reference(self.heap.len() - 1);
        self.value_stack.push(r);
        Ok(())
    }

    pub fn construct_struct(&mut self, n: u16) {
        let fields = self
            .value_stack
            .split_off(self.value_stack.len() - n as usize);
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::DynArray(fields)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    pub fn construct_array(&mut self, n: usize) {
        let elems = self.value_stack.split_off(self.value_stack.len() - n);
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::DynArray(elems)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    pub fn deconstruct(&mut self) {
        let obj = self.value_stack.pop().expect("stack underflow");
        match &obj {
            Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                ManagedObjectKind::DynArray(fields) => {
                    self.value_stack.extend(fields.iter().rev().cloned());
                }
                ManagedObjectKind::Enum { tag, value } => {
                    self.value_stack.push(value.clone());
                    self.push_int(*tag as AbraInt);
                }
                _ => panic!("not a tuple"),
            },
            _ => panic!("not a tuple"),
        };
    }

    pub fn increment_stack_base(&mut self, n: usize) {
        self.stack_base += n;
    }

    pub fn get_pending_effect(&self) -> Option<u16> {
        self.pending_effect
    }

    pub fn clear_pending_effect(&mut self) {
        self.pending_effect = None;
    }

    pub fn get_error(&self) -> &Option<VmError> {
        &self.error
    }

    fn make_error(&self, kind: VmErrorKind) -> VmError {
        VmError {
            kind,
            location: self.pc_to_error_location(self.pc),
            trace: self.make_trace(),
        }
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

    // Arithmetic
    Add,
    Subtract,
    Multiply,
    Divide,
    SquareRoot,
    Power,
    Modulo,

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
    CallExtern(usize),
    Return,
    Effect(u16),
    Panic,

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
    ArrayLength,
    ArrayPop,
    ConcatStrings,
    IntToString,
    FloatToString,

    LoadLib,
    LoadForeignFunc,
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
            Instr::Modulo => write!(f, "modulo"),
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
            Instr::PushString(s) => write!(f, "push_string {}", s),
            Instr::Jump(loc) => write!(f, "jump {}", loc),
            Instr::JumpIf(loc) => write!(f, "jump_if {}", loc),
            Instr::Call(loc) => write!(f, "call {}", loc),
            Instr::CallExtern(func_id) => write!(f, "call_extern {}", func_id),
            Instr::CallFuncObj => write!(f, "call_func_obj"),
            Instr::Return => write!(f, "return"),
            Instr::Panic => write!(f, "panic"),
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
            Instr::ArrayLength => write!(f, "array_len"),
            Instr::ArrayPop => write!(f, "array_pop"),
            Instr::ConcatStrings => write!(f, "concat_strings"),
            Instr::IntToString => write!(f, "int_to_string"),
            Instr::FloatToString => write!(f, "float_to_string"),
            Instr::Effect(n) => write!(f, "effect {}", n),

            Instr::LoadLib => write!(f, "load_lib"),
            Instr::LoadForeignFunc => write!(f, "load_foreign_func"),
        }
    }
}

#[repr(C)]
#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(AbraInt),
    Float(AbraFloat),
    HeapReference(Cell<HeapReference>),
}

#[repr(C)]
#[derive(Debug, Copy, Clone)]
pub struct HeapReference {
    idx: usize,
    group: HeapGroup,
}

impl HeapReference {
    fn get(&self) -> usize {
        self.idx
    }
}

#[repr(C)]
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum HeapGroup {
    One,
    Two,
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
    pub fn get_int(&self, vm: &Vm) -> AbraInt {
        match self {
            Value::Int(n) => *n,
            _ => panic!("not an int"),
        }
    }

    pub fn get_float(&self, vm: &Vm) -> AbraFloat {
        match self {
            Value::Float(f) => *f,
            _ => panic!("not a float"),
        }
    }

    pub fn get_bool(&self, vm: &Vm) -> Result<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            _ => Err(vm.make_error(VmErrorKind::WrongType)),
        }
    }

    pub fn get_string(&self, vm: &Vm) -> String {
        match self {
            Value::HeapReference(r) => {
                assert_eq!(r.get().group, vm.heap_group);
                match &vm.heap[r.get().get()].kind {
                    ManagedObjectKind::String(s) => s.clone(),
                    _ => panic!("not a string"),
                }
            }
            _ => panic!("not a string"),
        }
    }

    pub fn view_string<'a>(&self, vm: &'a Vm) -> &'a String {
        // println!("DURING FFI VM: {:#?}", vm);

        match self {
            Value::HeapReference(r) => match &vm.heap[r.get().get()].kind {
                ManagedObjectKind::String(s) => s,
                _ => panic!("not a string"),
            },
            _ => panic!("not a string"),
        }
    }

    pub fn get_tuple(&self, vm: &Vm) -> Vec<Value> {
        match self {
            Value::HeapReference(r) => match &vm.heap[r.get().get()].kind {
                ManagedObjectKind::DynArray(fields) => fields.clone(),
                _ => panic!("not a tuple"),
            },
            _ => panic!("not a tuple"),
        }
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_base: usize,
}

// ReferenceType
#[repr(C)]
#[derive(Debug, Clone)]
struct ManagedObject {
    kind: ManagedObjectKind,

    forwarding_pointer: Cell<Option<usize>>,
}

impl ManagedObject {
    fn new(kind: ManagedObjectKind) -> Self {
        Self {
            kind,
            forwarding_pointer: Cell::new(None),
        }
    }
}

#[repr(C)]
#[derive(Debug, Clone)]
enum ManagedObjectKind {
    Enum {
        tag: u16,
        value: Value,
    },
    // DynArray is also used for tuples and structs
    DynArray(Vec<Value>),
    String(String),
    FunctionObject {
        captured_values: Vec<Value>,
        func_addr: ProgramCounter,
    },
}

impl Vm {
    pub fn run(&mut self) {
        // for pair in &self.function_name_table {
        //     let function_name = &self.function_name_arena[pair.1 as usize];
        //     println!("bytecode[{}]\tfn {}()", pair.0, function_name);
        // }
        // println!("------------------------------------------------------");
        // for pair in &self.lineno_table {
        //     println!("bytecode[{}]\tline={}", pair.0, pair.1);
        // }
        // println!("------------------------------------------------------");
        // for pair in &self.filename_table {
        //     let filename = &self.filename_arena[pair.1 as usize];
        //     println!("bytecode[{}]\tfile '{}'", pair.0, filename);
        // }

        // if self.pc == 0 {
        //     for (i, instr) in self.program.iter().enumerate() {
        //         println!("{}", instr);
        //     }
        //     println!("----------------------------------------");
        // }

        if self.pending_effect.is_some() {
            panic!("must handle pending effect");
        }
        if self.error.is_some() {
            panic!("forgot to check error on vm");
        }
        while !self.is_done() && self.pending_effect.is_none() && self.error.is_none() {
            match self.step() {
                Ok(()) => {}
                Err(err) => self.error = Some(err),
            }
        }
    }

    pub fn run_n_steps(&mut self, steps: u32) {
        if self.pending_effect.is_some() {
            panic!("must handle pending effect");
        }
        if self.error.is_some() {
            panic!("must handle error");
        }
        let mut steps = steps;
        while steps > 0 && !self.is_done() && self.pending_effect.is_none() && self.error.is_none()
        {
            match self.step() {
                Ok(()) => {}
                Err(err) => self.error = Some(err),
            }
            steps -= 1;
        }
    }

    fn step(&mut self) -> Result<()> {
        let instr = self.program[self.pc];
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
                let s = &self.static_strings[idx as usize];
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s.clone())));
                let r = self.heap_reference(self.heap.len() - 1);
                self.value_stack.push(r);
            }
            Instr::Pop => {
                self.pop()?;
            }
            Instr::Duplicate => {
                let v = self.top();
                self.push(v.clone());
            }
            Instr::LoadOffset(n) => {
                let idx = self.stack_base.wrapping_add_signed(n as isize);
                let v = self.value_stack[idx].clone();
                self.push(v);
            }
            Instr::StoreOffset(n) => {
                let idx = self.stack_base.wrapping_add_signed(n as isize);
                let v = self.value_stack.pop().expect("stack underflow");
                self.value_stack[idx] = v;
            }
            Instr::Add => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a + b),
                    (Value::Float(a), Value::Float(b)) => self.push(a + b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Subtract => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a - b),
                    (Value::Float(a), Value::Float(b)) => self.push(a - b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Multiply => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a * b),
                    (Value::Float(a), Value::Float(b)) => self.push(a * b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Divide => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a / b),
                    (Value::Float(a), Value::Float(b)) => self.push(a / b),
                    _ => panic!("not a number"),
                }
            }
            Instr::SquareRoot => {
                let v = self.pop()?;
                match v {
                    Value::Float(f) => self.push(f.sqrt()),
                    _ => panic!("not a float"),
                }
            }
            Instr::Power => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a.pow(b as u32)),
                    (Value::Float(a), Value::Float(b)) => self.push(a.powf(b)),
                    _ => panic!("not a number"),
                }
            }
            Instr::Modulo => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a % b),
                    (Value::Float(a), Value::Float(b)) => self.push(a % b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Not => {
                let v = self.pop_bool()?;
                self.push(!v);
            }
            Instr::And => {
                let b = self.pop_bool()?;
                let a = self.pop_bool()?;
                self.push(a && b);
            }
            Instr::Or => {
                let b = self.pop_bool()?;
                let a = self.pop_bool()?;
                self.push(a || b);
            }
            Instr::LessThan => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a < b),
                    (Value::Float(a), Value::Float(b)) => self.push(a < b),
                    _ => panic!("not a number"),
                }
            }
            Instr::LessThanOrEqual => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a <= b),
                    (Value::Float(a), Value::Float(b)) => self.push(a <= b),
                    _ => panic!("not a number"),
                }
            }
            Instr::GreaterThan => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a > b),
                    (Value::Float(a), Value::Float(b)) => self.push(a > b),
                    _ => panic!("not a number"),
                }
            }
            Instr::GreaterThanOrEqual => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a >= b),
                    (Value::Float(a), Value::Float(b)) => self.push(a >= b),
                    _ => panic!("not a number"),
                }
            }
            Instr::Equal => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::Int(a), Value::Int(b)) => self.push(a == b),
                    (Value::Float(a), Value::Float(b)) => self.push(a == b),
                    (Value::Bool(a), Value::Bool(b)) => self.push(a == b),
                    (Value::HeapReference(a), Value::HeapReference(b)) => {
                        let a_idx = a.get().get();
                        let b_idx = b.get().get();
                        match (&self.heap[a_idx].kind, &self.heap[b_idx].kind) {
                            (ManagedObjectKind::String(a), ManagedObjectKind::String(b)) => {
                                self.push(a == b)
                            }
                            _ => self.push(false),
                        }
                    }
                    (Value::Nil, Value::Nil) => self.push(true),
                    _ => self.push(false),
                }
            }
            Instr::Jump(target) => {
                self.pc = target;
            }
            Instr::JumpIf(target) => {
                let v = self.pop_bool()?;
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
                    Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
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
                if self.call_stack.is_empty() {
                    self.pc = self.program.len();
                } else {
                    let frame = self.call_stack.pop().expect("call stack underflow");
                    self.pc = frame.pc;
                    self.stack_base = frame.stack_base;
                }
            }
            Instr::Panic => {
                let msg = self.pop_string();
                return Err(self.make_error(VmErrorKind::Panic(msg)));
            }
            Instr::Construct(n) => {
                let fields = self
                    .value_stack
                    .split_off(self.value_stack.len() - n as usize);
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::DynArray(fields)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.value_stack.push(r);
            }
            Instr::Deconstruct => {
                self.deconstruct();
            }
            Instr::GetField(index) => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let field = match &obj {
                    Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                        ManagedObjectKind::DynArray(fields) => fields[index as usize].clone(),
                        _ => panic!("not a tuple"),
                    },
                    _ => panic!("not a tuple"),
                };
                self.push(field);
            }
            Instr::SetField(index) => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let rvalue = self.value_stack.pop().expect("stack underflow");
                let obj_id = match obj {
                    Value::HeapReference(r) => r.get().get(),
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
                match &obj {
                    Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                        ManagedObjectKind::DynArray(fields) => {
                            if idx as usize >= fields.len() || idx < 0 {
                                return Err(self.make_error(VmErrorKind::ArrayOutOfBounds));
                            }
                            let field = fields[idx as usize].clone();
                            self.push(field);
                        }
                        _ => panic!("not a dynamic array"),
                    },
                    _ => panic!("not a dynamic array"),
                };
            }
            Instr::SetIdx => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let idx = self.pop_int();
                let rvalue = self.value_stack.pop().expect("stack underflow");
                let obj_id = match obj {
                    Value::HeapReference(r) => r.get().get(),
                    _ => panic!("not a managed object: {:?}", obj),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        if idx as usize >= fields.len() || idx < 0 {
                            return Err(self.make_error(VmErrorKind::ArrayOutOfBounds));
                        }
                        fields[idx as usize] = rvalue;
                    }
                    _ => panic!("not a dynamic array: {:?}", self.heap[obj_id]),
                }
            }
            Instr::ConstructVariant { tag } => {
                self.construct_variant(tag)?;
            }
            Instr::MakeClosure {
                n_captured,
                func_addr,
            } => {
                let captured_values = self
                    .value_stack
                    .split_off(self.value_stack.len() - n_captured as usize);
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::FunctionObject {
                        captured_values,
                        func_addr,
                    }));
                let r = self.heap_reference(self.heap.len() - 1);
                self.value_stack.push(r);
            }
            Instr::ArrayAppend => {
                let rvalue = self.pop()?;
                let obj = self.value_stack.pop().expect("stack underflow");
                let obj_id = match &obj {
                    Value::HeapReference(r) => r.get().get(),
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
            Instr::ArrayLength => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let len = match &obj {
                    Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                        ManagedObjectKind::DynArray(fields) => fields.len(),
                        _ => panic!("not a dynamic array"),
                    },
                    _ => panic!("not a dynamic array"),
                };
                self.push_int(len as AbraInt);
            }
            Instr::ArrayPop => {
                let obj = self.value_stack.pop().expect("stack underflow");
                let obj_id = match obj {
                    Value::HeapReference(r) => r.get().get(),
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
                let b = self.pop()?;
                let a = self.pop()?;
                let a_str = a.get_string(self);
                let b_str = b.get_string(self);
                let result = a_str + &b_str;
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(result)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.push(r);
            }
            Instr::IntToString => {
                let n = self.pop_int();
                let s = n.to_string();
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.push(r);
            }
            Instr::FloatToString => {
                let f = self.pop()?.get_float(self);
                let s = f.to_string();
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.push(r);
            }
            Instr::Effect(eff) => {
                self.pending_effect = Some(eff);
            }
            Instr::LoadLib => {
                if cfg!(not(feature = "ffi")) {
                    panic!("ffi is not enabled.")
                }

                #[cfg(feature = "ffi")]
                {
                    // pop libname from stack
                    // load the library with a certain name and add it to the Vm's Vec of libs
                    let libname = self.pop_string();
                    let lib = unsafe { Library::new(libname) };
                    let lib = lib.unwrap();
                    self.libs.push(lib);
                }
            }
            Instr::LoadForeignFunc => {
                if cfg!(not(feature = "ffi")) {
                    panic!("ffi is not enabled.")
                }

                #[cfg(feature = "ffi")]
                {
                    // pop foreign func name from stack
                    // load symbol from the last library loaded
                    let symbol_name = self.pop_string();
                    let lib = self.libs.last().unwrap();
                    let symbol /*: Result<libloading::Symbol<unsafe extern "C" fn(*mut Vm) -> ()>, _>*/ =
                        unsafe { lib.get(symbol_name.as_bytes()) };
                    let symbol = *symbol.unwrap();
                    self.foreign_functions.push(symbol);
                    // println!(
                    //     "foreign_functions[{}]={}",
                    //     self.foreign_functions.len() - 1,
                    //     symbol_name
                    // );
                }
            }
            Instr::CallExtern(_func_id) => {
                if cfg!(not(feature = "ffi")) {
                    panic!("ffi is not enabled.")
                }

                // println!("BEFORE FFI VM: {:#?}", &self);

                // println!(">>time to invoke func_id={}", _func_id);
                #[cfg(feature = "ffi")]
                {
                    unsafe {
                        let vm_ptr = self as *mut Vm;
                        self.foreign_functions[_func_id](vm_ptr);
                    };
                }

                // println!("AFTER FFI VM: {:#?}", &self);
            }
        }
        Ok(())
    }

    fn pc_to_error_location(&self, pc: usize) -> VmErrorLocation {
        let file_id = match self
            .filename_table
            .binary_search_by_key(&(pc as u32), |pair| pair.0)
        {
            Ok(idx) | Err(idx) => {
                let idx = if idx >= 1 { idx - 1 } else { idx };
                self.filename_table[idx].1
            }
        };

        let lineno = match self
            .lineno_table
            .binary_search_by_key(&(pc as u32), |pair| pair.0)
        {
            Ok(idx) | Err(idx) => {
                let idx = if idx >= 1 { idx - 1 } else { idx };
                self.lineno_table[idx].1
            }
        };

        let function_name_id = match self
            .function_name_table
            .binary_search_by_key(&(pc as u32), |pair| pair.0)
        {
            Ok(idx) | Err(idx) => {
                let idx = if idx >= 1 { idx - 1 } else { idx };
                self.function_name_table[idx].1
            }
        };

        let filename = self.filename_arena[file_id as usize].clone();
        let function_name = self.function_name_arena[function_name_id as usize].clone();

        VmErrorLocation {
            filename,
            lineno,
            function_name,
        }
    }

    fn make_trace(&self) -> Vec<VmErrorLocation> {
        let mut ret = vec![];
        for frame in &self.call_stack {
            ret.push(self.pc_to_error_location(frame.pc));
        }
        ret
    }

    fn heap_reference(&mut self, idx: usize) -> Value {
        Value::HeapReference(Cell::new(HeapReference {
            idx,
            group: self.heap_group,
        }))
    }

    pub fn compact(&mut self) {
        self.value_stack.shrink_to_fit();
        self.call_stack.shrink_to_fit();
    }

    pub fn nbytes(&self) -> usize {
        let mut n = self.program.len() * size_of::<Instr>()
            + self.value_stack.len() * size_of::<Value>()
            + self.call_stack.len() * size_of::<CallFrame>()
            + self.heap.len() * size_of::<ManagedObject>();

        n += self.static_strings.iter().map(|s| s.len()).sum::<usize>();
        n
    }

    pub fn heap_size(&self) -> usize {
        self.heap.len() * size_of::<ManagedObject>()
    }

    pub fn gc(&mut self) {
        let mut new_heap = Vec::<ManagedObject>::new();
        let new_heap_group = match self.heap_group {
            HeapGroup::One => HeapGroup::Two,
            HeapGroup::Two => HeapGroup::One,
        };

        // roots
        for i in 0..self.value_stack.len() {
            let v = &mut self.value_stack[i];
            if let Value::HeapReference(r) = v {
                r.replace(forward(
                    r.get(),
                    &self.heap,
                    0,
                    &mut new_heap,
                    new_heap_group,
                ));
            }
        }

        let mut i = 0;
        while i < new_heap.len() {
            let obj = &new_heap[i];
            let mut to_add: Vec<ManagedObject> = vec![];
            let new_heap_len = new_heap.len();
            match &obj.kind {
                ManagedObjectKind::DynArray(fields) => {
                    for v in fields {
                        if let Value::HeapReference(r) = v {
                            r.replace(forward(
                                r.get(),
                                &self.heap,
                                new_heap_len,
                                &mut to_add,
                                new_heap_group,
                            ));
                        }
                    }
                }
                ManagedObjectKind::FunctionObject {
                    captured_values,
                    func_addr: _,
                } => {
                    for v in captured_values {
                        if let Value::HeapReference(r) = v {
                            r.replace(forward(
                                r.get(),
                                &self.heap,
                                new_heap_len,
                                &mut to_add,
                                new_heap_group,
                            ));
                        }
                    }
                }
                ManagedObjectKind::Enum { tag: _, value } => {
                    if let Value::HeapReference(r) = value {
                        r.replace(forward(
                            r.get(),
                            &self.heap,
                            new_heap_len,
                            &mut to_add,
                            new_heap_group,
                        ));
                    }
                }
                ManagedObjectKind::String(_) => {}
            }

            new_heap.extend(to_add);

            i += 1;
        }

        mem::swap(&mut self.heap, &mut new_heap);
        self.heap_group = new_heap_group;

        // self.compact();
    }

    fn push(&mut self, x: impl Into<Value>) {
        self.value_stack.push(x.into());
    }

    fn pop_int(&mut self) -> AbraInt {
        self.value_stack
            .pop()
            .expect("stack underflow")
            .get_int(self)
    }

    fn pop_bool(&mut self) -> Result<bool> {
        self.pop()?.get_bool(self)
    }

    fn pop_string(&mut self) -> String {
        self.value_stack
            .pop()
            .expect("stack underflow")
            .get_string(self)
    }
}

fn forward(
    r: HeapReference,
    old_heap: &[ManagedObject],
    new_heap_len: usize,
    to_add: &mut Vec<ManagedObject>,
    new_heap_group: HeapGroup,
) -> HeapReference {
    if r.group != new_heap_group {
        // from space
        let old_obj = &old_heap[r.idx];
        match old_obj.forwarding_pointer.get() {
            Some(f) => {
                // return f
                HeapReference {
                    idx: f,
                    group: new_heap_group,
                }
            }
            None => {
                // copy to new heap and install forwarding pointer in old heap object
                let new_idx = to_add.len() + new_heap_len;

                let new_obj = old_obj.clone();
                new_obj.forwarding_pointer.replace(None);
                to_add.push(new_obj);

                old_obj.forwarding_pointer.replace(Some(new_idx));

                HeapReference {
                    idx: new_idx,
                    group: new_heap_group,
                }
            }
        }
    } else {
        // to space
        // this reference already points to the new heap
        r
    }
}

impl Debug for Vm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Vm")
            .field("pc", &self.pc)
            .field("stack_base", &self.stack_base)
            .field("value_stack", &format!("{:?}", self.value_stack))
            .field("call_stack", &format!("{:?}", self.call_stack))
            .field("heap", &format!("{:?}", self.heap))
            .field("program", &format!("{:?}", self.program))
            .finish()
    }
}

impl Error for VmError {}

impl Display for VmError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "error: {}", self.kind)?;
        let max_width = std::iter::once(&self.location)
            .chain(self.trace.iter())
            .map(|loc| loc.function_name.len() + "()".len())
            .max()
            .unwrap_or(10);
        for location in std::iter::once(&self.location).chain(self.trace.iter().rev()) {
            let func_call = format!("{}()", location.function_name);
            writeln!(
                f,
                "    from {:<max_width$} at {}, line {}",
                func_call, location.filename, location.lineno
            )?
        }
        Ok(())
    }
}

impl Display for VmErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VmErrorKind::ArrayOutOfBounds => {
                write!(f, "indexed past the end of an array")
            }
            VmErrorKind::Panic(msg) => {
                write!(f, "panic: {}", msg)
            }
            VmErrorKind::Underflow => {
                write!(f, "stack underflow")
            }
            VmErrorKind::WrongType => {
                write!(f, "wrong type on top of stack")
            }
        }
    }
}
