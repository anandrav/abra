/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

type ProgramCounter = usize;
pub type AbraInt = i64;
pub type AbraFloat = f64;

#[cfg(feature = "ffi")]
use crate::addons::ABRA_VM_FUNCS;
#[cfg(feature = "ffi")]
use crate::addons::AbraVmFunctions;
use crate::translate_bytecode::{BytecodeIndex, CompiledProgram};
use core::fmt;
#[cfg(feature = "ffi")]
use libloading::Library;
use std::error::Error;
#[cfg(feature = "ffi")]
use std::ffi::c_void;
use std::fmt::Debug;
use std::{
    cell::Cell,
    fmt::{Display, Formatter},
    mem,
};

pub type VmResult<T> = std::result::Result<T, Box<VmError>>;
type Result<T> = VmResult<T>;

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

    pending_host_func: Option<u16>,
    error: Option<Box<VmError>>,

    // FFI
    #[cfg(feature = "ffi")]
    libs: Vec<Library>,
    #[cfg(feature = "ffi")]
    foreign_functions: Vec<unsafe extern "C" fn(*mut c_void, *const AbraVmFunctions) -> ()>,
}

pub enum VmStatus {
    Done,
    PendingHostFunc(u16),
    OutOfSteps,
    Error(Box<VmError>),
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
    // user errors
    ArrayOutOfBounds,
    Panic(String),
    IntegerOverflowUnderflow,
    DivisionByZero,

    // internal errors AKA bugs
    Underflow,
    WrongType { expected: ValueKind },
    FfiNotEnabled,
    LibLoadFailure(String),
    SymbolLoadFailure(String),
    InternalError(String),
}

#[derive(Clone, Debug)]
pub enum ValueKind {
    Nil,
    Int,
    Float,
    Number, // TODO: make int and float specific instructions then remove this
    Bool,
    String,
    Array,
    Enum,
    Struct,
    Object, // TODO: make array, enum, struct specific instructions then remove this
    FunctionObject,
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

            static_strings: program.static_strings.into_iter().collect(),
            filename_arena: program.filename_arena.into_iter().collect(),
            function_name_arena: program.function_name_arena.into_iter().collect(),

            filename_table: program.filename_table,
            lineno_table: program.lineno_table,
            function_name_table: program.function_name_table,

            pending_host_func: None,
            error: None,

            #[cfg(feature = "ffi")]
            libs: Vec::new(),
            #[cfg(feature = "ffi")]
            foreign_functions: Vec::new(),
        }
    }

    pub fn with_entry_point(program: CompiledProgram, entry_point: String) -> Self {
        dbg!(&entry_point);
        let end = program.instructions.len();
        Self {
            program: program.instructions,
            pc: program.label_map[&entry_point],
            stack_base: 0,
            value_stack: Vec::new(),
            call_stack: vec![CallFrame {
                pc: end,
                stack_base: 0,
                stack_size: 1,
            }],
            heap: Vec::new(),
            heap_group: HeapGroup::One,

            static_strings: program.static_strings.into_iter().collect(),
            filename_arena: program.filename_arena.into_iter().collect(),
            function_name_arena: program.function_name_arena.into_iter().collect(),

            filename_table: program.filename_table,
            lineno_table: program.lineno_table,
            function_name_table: program.function_name_table,

            pending_host_func: None,
            error: None,

            #[cfg(feature = "ffi")]
            libs: Vec::new(),
            #[cfg(feature = "ffi")]
            foreign_functions: Vec::new(),
        }
    }

    pub fn status(&self) -> VmStatus {
        if let Some(eff) = self.pending_host_func {
            VmStatus::PendingHostFunc(eff)
        } else if self.is_done() {
            VmStatus::Done
        } else {
            match &self.error {
                Some(err) => VmStatus::Error(err.clone()),
                _ => VmStatus::OutOfSteps,
            }
        }
    }

    pub fn top(&self) -> Result<&Value> {
        match self.value_stack.last() {
            Some(v) => Ok(v),
            None => self.make_error(VmErrorKind::Underflow),
        }
    }

    pub fn pop(&mut self) -> Result<Value> {
        match self.value_stack.pop() {
            Some(v) => Ok(v),
            None => self.make_error(VmErrorKind::Underflow),
        }
    }

    pub fn pop_n(&mut self, n: usize) -> Result<Vec<Value>> {
        if n > self.value_stack.len() {
            return self.make_error(VmErrorKind::Underflow);
        }
        Ok(self
            .value_stack
            .drain(self.value_stack.len() - n..)
            .collect())
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

    pub fn construct_tuple(&mut self, n: u16) -> Result<()> {
        self.construct_impl(n as usize)
    }

    pub fn construct_variant(&mut self, tag: u16) -> Result<()> {
        let value = self.pop()?;
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::Enum { tag, value }));
        let r = self.heap_reference(self.heap.len() - 1);
        self.value_stack.push(r);
        Ok(())
    }

    pub fn construct_struct(&mut self, n: u16) -> Result<()> {
        self.construct_impl(n as usize)
    }

    pub fn construct_array(&mut self, n: usize) -> Result<()> {
        self.construct_impl(n)
    }

    fn construct_impl(&mut self, n: usize) -> Result<()> {
        let fields = self.pop_n(n)?;
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::DynArray(fields)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
        Ok(())
    }

    pub fn deconstruct(&mut self) -> Result<()> {
        let obj = self.pop()?;
        match &obj {
            Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                ManagedObjectKind::DynArray(fields) => {
                    self.value_stack.extend(fields.iter().rev().cloned());
                }
                ManagedObjectKind::Enum { tag, value } => {
                    self.value_stack.push(value.clone());
                    self.push_int(*tag as AbraInt);
                }
                _ => return self.wrong_type(ValueKind::Object),
            },
            _ => return self.wrong_type(ValueKind::Object),
        };
        Ok(())
    }

    pub fn array_len(&mut self) -> Result<usize> {
        let obj = self.top()?;
        let len = match &obj {
            Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                ManagedObjectKind::DynArray(fields) => fields.len(),
                _ => return self.wrong_type(ValueKind::Array),
            },
            _ => return self.wrong_type(ValueKind::Array),
        };
        Ok(len)
    }

    pub fn increment_stack_base(&mut self, n: usize) {
        self.stack_base += n;
    }

    pub fn get_pending_host_func(&self) -> Option<u16> {
        self.pending_host_func
    }

    pub fn clear_pending_host_func(&mut self) {
        self.pending_host_func = None;
    }

    pub fn get_error(&self) -> Option<Box<VmError>> {
        self.error.clone()
    }

    fn make_error<T>(&self, kind: VmErrorKind) -> Result<T> {
        Err(Box::new(VmError {
            kind,
            location: self.pc_to_error_location(self.pc),
            trace: self.make_stack_trace(),
        }))
    }

    fn wrong_type<T>(&self, expected: ValueKind) -> Result<T> {
        Err(Box::new(VmError {
            kind: VmErrorKind::WrongType { expected },
            location: self.pc_to_error_location(self.pc),
            trace: self.make_stack_trace(),
        }))
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
    AddInt,
    SubtractInt,
    MultiplyInt,
    DivideInt,
    PowerInt,
    Modulo,

    AddFloat,
    SubtractFloat,
    MultiplyFloat,
    DivideFloat,
    PowerFloat,

    SquareRoot,

    // Logical
    Not,
    And,
    Or,

    // Comparison
    LessThanInt,
    LessThanOrEqualInt,
    GreaterThanInt,
    GreaterThanOrEqualInt,
    LessThanFloat,
    LessThanOrEqualFloat,
    GreaterThanFloat,
    GreaterThanOrEqualFloat,
    EqualInt,
    EqualFloat,
    EqualBool,
    EqualString, // TODO: this is O(N). Must use smaller instructions

    // Control Flow
    Jump(Location),
    JumpIf(Location),
    Call(Location),
    CallFuncObj,
    CallExtern(usize),
    Return,
    HostFunc(u16),
    Panic,

    // Data Structures
    Construct(u16),
    Deconstruct,
    GetField(u16),
    SetField(u16),
    GetIdx,
    SetIdx,
    ConstructVariant { tag: u16 },
    MakeClosure { func_addr: Location },

    ArrayAppend,
    ArrayLength,
    ArrayPop,
    ConcatStrings, // TODO: this is O(N). Must use smaller instructions
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
            Instr::LoadOffset(n) => write!(f, "loadOffset {n}"),
            Instr::StoreOffset(n) => write!(f, "storeOffset {n}"),
            Instr::AddInt => write!(f, "add_int"),
            Instr::SubtractInt => write!(f, "subtract_int"),
            Instr::MultiplyInt => write!(f, "multiply_int"),
            Instr::DivideInt => write!(f, "divide_int"),
            Instr::PowerInt => write!(f, "power_int"),
            Instr::Modulo => write!(f, "modulo"),
            Instr::AddFloat => write!(f, "add_float"),
            Instr::SubtractFloat => write!(f, "subtract_float"),
            Instr::MultiplyFloat => write!(f, "multiply_float"),
            Instr::DivideFloat => write!(f, "divide_float"),
            Instr::PowerFloat => write!(f, "power_float"),
            Instr::SquareRoot => write!(f, "square_root"),
            Instr::Not => write!(f, "not"),
            Instr::And => write!(f, "and"),
            Instr::Or => write!(f, "or"),
            Instr::LessThanInt => write!(f, "less_than_int"),
            Instr::LessThanOrEqualInt => write!(f, "less_than_or_equal_int"),
            Instr::GreaterThanInt => write!(f, "greater_than_int"),
            Instr::GreaterThanOrEqualInt => write!(f, "greater_than_or_equal_int"),
            Instr::LessThanFloat => write!(f, "less_than_float"),
            Instr::LessThanOrEqualFloat => write!(f, "less_than_or_equal_float"),
            Instr::GreaterThanFloat => write!(f, "greater_than_float"),
            Instr::GreaterThanOrEqualFloat => write!(f, "greater_than_or_equal_float"),
            Instr::EqualInt => write!(f, "equal_int"),
            Instr::EqualFloat => write!(f, "equal_float"),
            Instr::EqualBool => write!(f, "equal_bool"),
            Instr::EqualString => write!(f, "equal_string"),
            Instr::PushNil => write!(f, "push_nil"),
            Instr::PushBool(b) => write!(f, "push_bool {b}"),
            Instr::PushInt(n) => write!(f, "push_int {n}"),
            Instr::PushFloat(n) => write!(f, "push_float {n}"),
            Instr::PushString(s) => write!(f, "push_string {s}"),
            Instr::Jump(loc) => write!(f, "jump {loc}"),
            Instr::JumpIf(loc) => write!(f, "jump_if {loc}"),
            Instr::Call(loc) => write!(f, "call {loc}"),
            Instr::CallExtern(func_id) => write!(f, "call_extern {func_id}"),
            Instr::CallFuncObj => write!(f, "call_func_obj"),
            Instr::Return => write!(f, "return"),
            Instr::Panic => write!(f, "panic"),
            Instr::Construct(n) => write!(f, "construct {n}"),
            Instr::Deconstruct => write!(f, "deconstruct"),
            Instr::GetField(n) => write!(f, "get_field {n}"),
            Instr::SetField(n) => write!(f, "set_field {n}"),
            Instr::GetIdx => write!(f, "get_index"),
            Instr::SetIdx => write!(f, "set_index"),
            Instr::ConstructVariant { tag } => {
                write!(f, "construct_variant {tag}")
            }
            Instr::MakeClosure { func_addr } => {
                write!(f, "make_closure {func_addr}")
            }
            Instr::ArrayAppend => write!(f, "array_append"),
            Instr::ArrayLength => write!(f, "array_len"),
            Instr::ArrayPop => write!(f, "array_pop"),
            Instr::ConcatStrings => write!(f, "concat_strings"),
            Instr::IntToString => write!(f, "int_to_string"),
            Instr::FloatToString => write!(f, "float_to_string"),
            Instr::HostFunc(n) => write!(f, "call_host {n}"),

            Instr::LoadLib => write!(f, "load_lib"),
            Instr::LoadForeignFunc => write!(f, "load_foreign_func"),
        }
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Nil,
    Bool(bool),
    Int(AbraInt),
    Float(AbraFloat),
    FuncAddr(usize),
    HeapReference(Cell<HeapReference>),
}

#[derive(Debug, Copy, Clone)]
pub struct HeapReference {
    idx: u32,
    group: HeapGroup,
}

impl HeapReference {
    fn get(&self) -> usize {
        self.idx as usize
    }
}

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
    pub fn get_int(&self, vm: &Vm) -> Result<AbraInt> {
        match self {
            Value::Int(i) => Ok(*i),
            _ => vm.wrong_type(ValueKind::Int),
        }
    }

    pub fn get_float(&self, vm: &Vm) -> Result<AbraFloat> {
        match self {
            Value::Float(f) => Ok(*f),
            _ => vm.wrong_type(ValueKind::Int),
        }
    }

    pub fn get_bool(&self, vm: &Vm) -> Result<bool> {
        match self {
            Value::Bool(b) => Ok(*b),
            _ => vm.wrong_type(ValueKind::Bool),
        }
    }

    pub fn view_string<'a>(&self, vm: &'a Vm) -> Result<&'a String> {
        match self {
            Value::HeapReference(r) => match &vm.heap[r.get().get()].kind {
                ManagedObjectKind::String(s) => Ok(s),
                _ => vm.wrong_type(ValueKind::String),
            },
            _ => vm.wrong_type(ValueKind::String),
        }
    }

    pub fn get_addr(&self, vm: &Vm) -> Result<usize> {
        match self {
            Value::FuncAddr(addr) => Ok(*addr),
            _ => vm.wrong_type(ValueKind::Int),
        }
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_base: usize,
    stack_size: usize,
}

// ReferenceType

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

#[derive(Debug, Clone)]
enum ManagedObjectKind {
    Enum { tag: u16, value: Value },
    // DynArray is also used for tuples and structs
    DynArray(Vec<Value>),
    String(String),
}

impl Vm {
    pub fn run(&mut self) {
        if self.pending_host_func.is_some() {
            panic!("must handle pending host func");
        }
        if self.error.is_some() {
            panic!("forgot to check error on vm");
        }
        while !self.is_done() && self.pending_host_func.is_none() && self.error.is_none() {
            match self.step() {
                Ok(()) => {}
                Err(err) => self.error = Some(err),
            }
        }
    }

    pub fn run_n_steps(&mut self, steps: u32) {
        if self.pending_host_func.is_some() {
            panic!("must handle pending host func");
        }
        if self.error.is_some() {
            panic!("must handle error");
        }
        let mut steps = steps;
        while steps > 0
            && !self.is_done()
            && self.pending_host_func.is_none()
            && self.error.is_none()
        {
            match self.step() {
                Ok(()) => {}
                Err(err) => self.error = Some(err),
            }
            steps -= 1;
        }
    }

    fn step(&mut self) -> Result<()> {
        // dbg!(&self);
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
                let v = self.top()?;
                self.push(v.clone());
            }
            Instr::LoadOffset(n) => {
                let idx = match self.stack_base.checked_add_signed(n as isize) {
                    Some(idx) => idx,
                    None => {
                        return self.make_error(VmErrorKind::InternalError(format!(
                            "overflow when calculating load offset ({n})"
                        )));
                    }
                };
                let v = if idx < self.value_stack.len() {
                    self.value_stack[idx].clone()
                } else {
                    return self.make_error(VmErrorKind::InternalError(format!(
                        "load offset ({}) out of bounds. idx={}, len={}",
                        n,
                        idx,
                        self.value_stack.len()
                    )));
                };
                self.push(v);
            }
            Instr::StoreOffset(n) => {
                let idx = match self.stack_base.checked_add_signed(n as isize) {
                    Some(idx) => idx,
                    None => {
                        return self.make_error(VmErrorKind::InternalError(format!(
                            "overflow when calculating store offset ({n})"
                        )));
                    }
                };
                let v = self.pop()?;
                if idx < self.value_stack.len() {
                    self.value_stack[idx] = v;
                } else {
                    return self.make_error(VmErrorKind::InternalError(format!(
                        "store offset ({}) out of bounds. idx={}, len={}",
                        n,
                        idx,
                        self.value_stack.len()
                    )));
                }
            }
            Instr::AddInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                match a.checked_add(b) {
                    Some(n) => self.push(n),
                    None => return self.make_error(VmErrorKind::IntegerOverflowUnderflow),
                }
            }
            Instr::SubtractInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                match a.checked_sub(b) {
                    Some(n) => self.push(n),
                    None => return self.make_error(VmErrorKind::IntegerOverflowUnderflow),
                }
            }
            Instr::MultiplyInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                match a.checked_mul(b) {
                    Some(n) => self.push(n),
                    None => return self.make_error(VmErrorKind::IntegerOverflowUnderflow),
                }
            }
            Instr::DivideInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                if b == 0 {
                    return self.make_error(VmErrorKind::DivisionByZero);
                }
                match a.checked_div(b) {
                    Some(n) => self.push(n),
                    None => return self.make_error(VmErrorKind::IntegerOverflowUnderflow),
                }
            }
            Instr::PowerInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a.pow(b as u32));
            }
            Instr::Modulo => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a % b);
            }
            Instr::AddFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a + b);
            }
            Instr::SubtractFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a - b);
            }
            Instr::MultiplyFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a * b);
            }
            Instr::DivideFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                if b == 0.0 {
                    return self.make_error(VmErrorKind::DivisionByZero);
                }
                self.push(a / b);
            }
            Instr::PowerFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a.powf(b));
            }
            Instr::SquareRoot => {
                let v = self.pop_float()?;
                self.push(v.sqrt());
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
            Instr::LessThanInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a < b);
            }
            Instr::LessThanOrEqualInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a <= b);
            }
            Instr::GreaterThanInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a > b);
            }
            Instr::GreaterThanOrEqualInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a >= b);
            }
            Instr::LessThanFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a < b);
            }
            Instr::LessThanOrEqualFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a <= b);
            }
            Instr::GreaterThanFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a > b);
            }
            Instr::GreaterThanOrEqualFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a >= b);
            }
            Instr::EqualInt => {
                let b = self.pop_int()?;
                let a = self.pop_int()?;
                self.push(a == b);
            }
            Instr::EqualFloat => {
                let b = self.pop_float()?;
                let a = self.pop_float()?;
                self.push(a == b);
            }
            Instr::EqualBool => {
                let b = self.pop_bool()?;
                let a = self.pop_bool()?;
                self.push(a == b);
            }
            Instr::EqualString => {
                let b = self.pop()?;
                let a = self.pop()?;
                match (a, b) {
                    (Value::HeapReference(a), Value::HeapReference(b)) => {
                        let a_idx = a.get().get();
                        let b_idx = b.get().get();
                        match (&self.heap[a_idx].kind, &self.heap[b_idx].kind) {
                            (ManagedObjectKind::String(a), ManagedObjectKind::String(b)) => {
                                self.push(a == b)
                            }
                            _ => {
                                return self.wrong_type(ValueKind::String);
                            }
                        }
                    }
                    _ => {
                        return self.wrong_type(ValueKind::String);
                    }
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
                let nargs = self.pop_int()?;
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_base: self.stack_base,
                    stack_size: self.value_stack.len() - nargs as usize + 1,
                });
                self.pc = target;
                self.stack_base = self.value_stack.len();
            }
            Instr::CallFuncObj => {
                let nargs = self.pop_int()?;
                let addr = self.pop_addr()?;
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_base: self.stack_base,
                    stack_size: self.value_stack.len() - nargs as usize + 1,
                });
                self.pc = addr;
                self.stack_base = self.value_stack.len();
            }
            Instr::Return => {
                if self.call_stack.is_empty() {
                    self.pc = self.program.len();
                } else {
                    let frame = self.call_stack.pop();
                    let Some(frame) = frame else {
                        return self.make_error(VmErrorKind::Underflow);
                    };
                    self.pc = frame.pc;
                    self.stack_base = frame.stack_base;
                    self.value_stack.truncate(frame.stack_size);
                }
            }
            Instr::Panic => {
                let msg = self.pop()?.view_string(self)?;
                return self.make_error(VmErrorKind::Panic(msg.clone()));
            }
            Instr::Construct(n) => self.construct_impl(n as usize)?,
            Instr::Deconstruct => {
                self.deconstruct()?;
            }
            Instr::GetField(index) => {
                let obj = self.pop()?;
                let field = match &obj {
                    Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                        ManagedObjectKind::DynArray(fields) => fields[index as usize].clone(),
                        _ => return self.wrong_type(ValueKind::Struct),
                    },
                    _ => return self.wrong_type(ValueKind::Struct),
                };
                self.push(field);
            }
            Instr::SetField(index) => {
                let obj = self.pop()?;
                let rvalue = self.pop()?;
                let obj_id = match obj {
                    Value::HeapReference(r) => r.get().get(),
                    _ => return self.wrong_type(ValueKind::Struct),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        fields[index as usize] = rvalue;
                    }
                    _ => return self.wrong_type(ValueKind::Struct),
                }
            }
            Instr::GetIdx => {
                let obj = self.pop()?;
                let idx = self.pop_int()?;
                match &obj {
                    Value::HeapReference(r) => match &self.heap[r.get().get()].kind {
                        ManagedObjectKind::DynArray(fields) => {
                            if idx as usize >= fields.len() || idx < 0 {
                                return self.make_error(VmErrorKind::ArrayOutOfBounds);
                            }
                            let field = fields[idx as usize].clone();
                            self.push(field);
                        }
                        _ => return self.wrong_type(ValueKind::Array),
                    },
                    _ => return self.wrong_type(ValueKind::Array),
                };
            }
            Instr::SetIdx => {
                let obj = self.pop()?;
                let idx = self.pop_int()?;
                let rvalue = self.pop()?;
                let obj_id = match obj {
                    Value::HeapReference(r) => r.get().get(),
                    _ => return self.wrong_type(ValueKind::Array),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        if idx as usize >= fields.len() || idx < 0 {
                            return self.make_error(VmErrorKind::ArrayOutOfBounds);
                        }
                        fields[idx as usize] = rvalue;
                    }
                    _ => return self.wrong_type(ValueKind::Array),
                }
            }
            Instr::ConstructVariant { tag } => {
                self.construct_variant(tag)?;
            }
            Instr::MakeClosure { func_addr } => {
                self.value_stack.push(Value::FuncAddr(func_addr));
            }
            Instr::ArrayAppend => {
                let rvalue = self.pop()?;
                let obj = self.pop()?;
                let obj_id = match &obj {
                    Value::HeapReference(r) => r.get().get(),
                    _ => return self.wrong_type(ValueKind::Array),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        fields.push(rvalue);
                    }
                    _ => return self.wrong_type(ValueKind::Array),
                }
                self.push_nil();
            }
            Instr::ArrayLength => {
                let len = self.array_len()?;
                self.push_int(len as AbraInt);
            }
            Instr::ArrayPop => {
                let obj = self.pop()?;
                let obj_id = match obj {
                    Value::HeapReference(r) => r.get().get(),
                    _ => return self.wrong_type(ValueKind::Array),
                };
                match &mut self.heap[obj_id].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        let rvalue = fields.pop().expect("array underflow");
                        self.push(rvalue);
                    }
                    _ => return self.wrong_type(ValueKind::Array),
                }
            }
            Instr::ConcatStrings => {
                let b = self.pop()?;
                let a = self.pop()?;
                let a_str = a.view_string(self)?;
                let b_str = b.view_string(self)?;
                let mut new_str = String::new();
                new_str.push_str(a_str);
                new_str.push_str(b_str);
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(new_str)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.push(r);
            }
            Instr::IntToString => {
                let n = self.pop_int()?;
                let s = n.to_string();
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.push(r);
            }
            Instr::FloatToString => {
                let f = self.pop()?.get_float(self)?;
                let s = f.to_string();
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.push(r);
            }
            Instr::HostFunc(eff) => {
                self.pending_host_func = Some(eff);
            }
            Instr::LoadLib => {
                if cfg!(not(feature = "ffi")) {
                    return self.make_error(VmErrorKind::FfiNotEnabled);
                }

                #[cfg(feature = "ffi")]
                {
                    // pop libname from stack
                    // load the library with a certain name and add it to the Vm's Vec of libs
                    let libname = self.pop()?.view_string(self)?;
                    let lib = unsafe { Library::new(libname) };
                    let Ok(lib) = lib else {
                        return self.make_error(VmErrorKind::LibLoadFailure(libname.clone()));
                    };
                    self.libs.push(lib);
                }
            }
            Instr::LoadForeignFunc => {
                if cfg!(not(feature = "ffi")) {
                    return self.make_error(VmErrorKind::FfiNotEnabled);
                }

                #[cfg(feature = "ffi")]
                {
                    // pop foreign func name from stack
                    // load symbol from the last library loaded
                    let symbol_name = self.pop()?.view_string(self)?;
                    let lib = self.libs.last().expect("no libraries have been loaded");
                    let symbol /*: Result<libloading::Symbol<unsafe extern "C" fn(*mut Vm) -> ()>, _>*/ =
                        unsafe { lib.get(symbol_name.as_bytes()) };
                    let Ok(symbol) = symbol else {
                        return self
                            .make_error(VmErrorKind::SymbolLoadFailure(symbol_name.clone()));
                    };
                    self.foreign_functions.push(*symbol);
                }
            }
            Instr::CallExtern(_func_id) => {
                if cfg!(not(feature = "ffi")) {
                    return self.make_error(VmErrorKind::FfiNotEnabled);
                }

                #[cfg(feature = "ffi")]
                {
                    unsafe {
                        let vm_ptr = self as *mut Vm as *mut c_void;
                        let abra_vm_functions_ptr = &ABRA_VM_FUNCS as *const AbraVmFunctions;
                        self.foreign_functions[_func_id](vm_ptr, abra_vm_functions_ptr);
                    };
                }
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

    fn make_stack_trace(&self) -> Vec<VmErrorLocation> {
        let mut ret = vec![];
        for frame in &self.call_stack {
            ret.push(self.pc_to_error_location(frame.pc));
        }
        ret
    }

    fn heap_reference(&mut self, idx: usize) -> Value {
        Value::HeapReference(Cell::new(HeapReference {
            idx: idx as u32,
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

    pub fn pop_int(&mut self) -> Result<AbraInt> {
        self.pop()?.get_int(self)
    }

    pub fn pop_float(&mut self) -> Result<AbraFloat> {
        self.pop()?.get_float(self)
    }

    fn pop_addr(&mut self) -> Result<usize> {
        self.pop()?.get_addr(self)
    }

    fn pop_bool(&mut self) -> Result<bool> {
        self.pop()?.get_bool(self)
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
        let old_obj = &old_heap[r.get()];
        match old_obj.forwarding_pointer.get() {
            Some(f) => {
                // return f
                HeapReference {
                    idx: f as u32,
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
                    idx: new_idx as u32,
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
            // .field("program", &format!("{:?}", self.program))
            .finish()
    }
}

impl Error for VmError {}

impl Display for VmError {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        writeln!(f, "{}", self.kind)?;
        let width = std::iter::once(&self.location)
            .chain(self.trace.iter())
            .map(|loc| loc.filename.len() + /*colon*/ 1 + loc.lineno.to_string().len()) // todo count digits of lineno w/out converting to string
            .max()
            .unwrap_or(10);
        writeln!(f, "[traceback]")?;
        for location in std::iter::once(&self.location).chain(self.trace.iter().rev()) {
            let file_and_line = format!("{}:{}", location.filename, location.lineno);
            writeln!(
                f,
                "    {:width$} in `{}`",
                file_and_line, location.function_name
            )?
        }
        Ok(())
    }
}

impl Display for VmErrorKind {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            VmErrorKind::ArrayOutOfBounds => {
                write!(f, "error: indexed past the end of an array")
            }
            VmErrorKind::Panic(msg) => {
                write!(f, "panic: `{msg}`")
            }
            VmErrorKind::IntegerOverflowUnderflow => {
                write!(f, "error: integer overflow/underflow")
            }
            VmErrorKind::DivisionByZero => {
                write!(f, "error: division by zero")
            }
            VmErrorKind::FfiNotEnabled => {
                write!(f, "ffi is not enabled")
            }
            VmErrorKind::LibLoadFailure(s) => {
                write!(f, "failed to load shared library: {s}")
            }
            VmErrorKind::SymbolLoadFailure(s) => {
                write!(f, "failed to load symbol: {s}")
            }
            VmErrorKind::InternalError(s) => {
                write!(f, "internal error: {s}")
            }
            VmErrorKind::WrongType { expected } => {
                write!(
                    f,
                    "internal error: wrong type on top of stack, expected: {expected:?}"
                )
            }
            VmErrorKind::Underflow => {
                write!(f, "internal error: stack underflow")
            }
        }
    }
}
