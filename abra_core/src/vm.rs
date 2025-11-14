/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#[derive(Copy, Clone, Debug)]
pub struct ProgramCounter(pub u32);
impl ProgramCounter {
    pub(crate) fn new(n: usize) -> Self {
        ProgramCounter(n as u32)
    }
    pub(crate) fn get(self) -> usize {
        self.0 as usize
    }
}
impl Display for ProgramCounter {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}
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

pub struct Vm<Value: ValueTrait = PackedValue> {
    program: Vec<Instr>,
    pc: ProgramCounter,
    stack_base: usize,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    heap: Vec<ManagedObject<Value>>,
    heap_group: HeapGroup,

    int_constants: Vec<i64>,
    float_constants: Vec<f64>,
    static_strings: Vec<String>,
    filename_arena: Vec<String>,
    function_name_arena: Vec<String>,

    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,

    pending_host_func: Option<u16>,
    error: Option<Box<VmError>>,
    done: bool,

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
    Bool,
    String,
    Array,
    Enum,
    Struct,
    HeapObject,
    FunctionObject,
}

pub type ErrorLocation = (String, u32);

impl Vm {
    pub fn new(program: CompiledProgram) -> Self {
        Self {
            program: program.instructions,
            pc: ProgramCounter(0),
            // stack[0] is return value from main
            stack_base: 1,
            // the nil is placeholder for return value from main
            value_stack: vec![PackedValue::make_nil()],
            call_stack: Vec::new(),
            heap: Vec::new(),
            heap_group: HeapGroup::One,

            int_constants: program.int_constants.into_iter().collect(),
            float_constants: program.float_constants.into_iter().collect(),
            static_strings: program.static_strings.into_iter().collect(),
            filename_arena: program.filename_arena.into_iter().collect(),
            function_name_arena: program.function_name_arena.into_iter().collect(),

            filename_table: program.filename_table,
            lineno_table: program.lineno_table,
            function_name_table: program.function_name_table,

            pending_host_func: None,
            error: None,
            done: false,

            #[cfg(feature = "ffi")]
            libs: Vec::new(),
            #[cfg(feature = "ffi")]
            foreign_functions: Vec::new(),
        }
    }
}

impl<Value: ValueTrait> Vm<Value> {
    // pub fn with_entry_point(program: CompiledProgram, entry_point: String) -> Option<Self> {
    //     dbg!(&entry_point);
    //     dbg!(&program.label_map);
    //     let pc = *program.label_map.get(&entry_point);
    //     Some(Self {
    //         program: program.instructions,
    //         pc,
    //         stack_base: 0,
    //         value_stack: Vec::new(),
    //         call_stack: Vec::new(),
    //         heap: Vec::new(),
    //         heap_group: HeapGroup::One,
    //
    //         static_strings: program.static_strings.into_iter().collect(),
    //         filename_arena: program.filename_arena.into_iter().collect(),
    //         function_name_arena: program.function_name_arena.into_iter().collect(),
    //
    //         filename_table: program.filename_table,
    //         lineno_table: program.lineno_table,
    //         function_name_table: program.function_name_table,
    //
    //         pending_host_func: None,
    //         error: None,
    //
    //         #[cfg(feature = "ffi")]
    //         libs: Vec::new(),
    //         #[cfg(feature = "ffi")]
    //         foreign_functions: Vec::new(),
    //     })
    // }

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

    #[inline(always)]
    pub fn top(&self) -> &Value {
        match self.value_stack.last() {
            Some(v) => v,
            None => panic!("stack is empty"),
        }
    }

    #[inline(always)]
    fn set_top(&mut self, val: impl Into<Value>) {
        let len = self.value_stack.len();
        self.value_stack[len - 1] = val.into();
    }

    #[inline(always)]
    pub fn load_offset(&self, offset: i16) -> &Value {
        &self.value_stack[self.stack_base.wrapping_add_signed(offset as isize)]
    }

    #[inline(always)]
    pub fn pop(&mut self) -> Value {
        match self.value_stack.pop() {
            Some(v) => v,
            None => panic!("underflow"),
        }
    }

    #[inline(always)]
    pub fn pop_n(&mut self, n: usize) -> Vec<Value> {
        self.value_stack
            .drain(self.value_stack.len() - n..)
            .collect()
    }

    #[inline(always)]
    pub fn push_int(&mut self, n: AbraInt) {
        self.push(n);
    }

    #[inline(always)]
    pub fn push_str(&mut self, s: String) {
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::String(s)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    #[inline(always)]
    pub fn push_nil(&mut self) {
        self.push(Value::make_nil());
    }

    #[inline(always)]
    pub fn push_bool(&mut self, b: bool) {
        self.push(b);
    }

    #[inline(always)]
    pub fn push_float(&mut self, f: AbraFloat) {
        self.push(f);
    }

    #[inline(always)]
    pub fn construct_variant(&mut self, tag: u16) {
        let value = self.top();
        self.heap.push(ManagedObject::new(ManagedObjectKind::Enum {
            tag,
            value: *value,
        }));
        let r = self.heap_reference(self.heap.len() - 1);
        self.set_top(r);
    }

    #[inline(always)]
    pub fn construct_tuple(&mut self, n: usize) {
        self.construct_struct(n)
    }

    #[inline(always)]
    pub fn construct_struct(&mut self, n: usize) {
        let fields = self.pop_n(n);
        let fields = fields.into_boxed_slice();
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::Struct(fields)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    #[inline(always)]
    pub fn construct_array(&mut self, n: usize) {
        let fields = self.pop_n(n);
        self.heap
            .push(ManagedObject::new(ManagedObjectKind::DynArray(fields)));
        let r = self.heap_reference(self.heap.len() - 1);
        self.push(r);
    }

    #[inline(always)]
    pub fn deconstruct_struct(&mut self) {
        let obj = self.pop();
        let heap_index = obj.get_heap_index(self, ValueKind::Struct);
        match &self.heap[heap_index].kind {
            ManagedObjectKind::Struct(fields) => {
                self.value_stack.extend(fields.iter().rev().cloned());
            }
            _ => self.fail_wrong_type(ValueKind::Struct),
        }
    }

    #[inline(always)]
    pub fn deconstruct_array(&mut self) {
        let obj = self.pop();
        let heap_index = obj.get_heap_index(self, ValueKind::Struct);
        match &self.heap[heap_index].kind {
            ManagedObjectKind::DynArray(fields) => {
                self.value_stack.extend(fields.iter().rev().cloned());
            }
            _ => self.fail_wrong_type(ValueKind::Array),
        }
    }

    #[inline(always)]
    pub fn deconstruct_variant(&mut self) {
        let obj = self.top();
        let heap_index = obj.get_heap_index(self, ValueKind::Enum);
        let (value, tag) = match &self.heap[heap_index].kind {
            ManagedObjectKind::Enum { tag, value } => (*value, *tag),
            _ => self.fail_wrong_type(ValueKind::Enum),
        };
        self.set_top(value);
        self.push(tag as AbraInt);
    }

    #[inline(always)]
    pub fn array_len(&mut self) -> usize {
        let obj = self.top();
        let index = obj.get_heap_index(self, ValueKind::Array);
        match &self.heap[index].kind {
            ManagedObjectKind::DynArray(fields) => fields.len(),
            _ => self.fail_wrong_type(ValueKind::Array),
        }
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

    #[inline(always)]
    fn fail(&self, kind: VmErrorKind) -> ! {
        panic!(
            "{}",
            VmError {
                kind,
                location: self.pc_to_error_location(self.pc),
                trace: self.make_stack_trace(),
            }
        )
    }

    #[inline(always)]
    fn make_error(&self, kind: VmErrorKind) -> VmError {
        VmError {
            kind,
            location: self.pc_to_error_location(self.pc),
            trace: self.make_stack_trace(),
        }
    }

    #[inline(always)]
    fn fail_wrong_type(&self, expected: ValueKind) -> ! {
        panic!(
            "{}",
            VmError {
                kind: VmErrorKind::WrongType { expected },
                location: self.pc_to_error_location(self.pc),
                trace: self.make_stack_trace(),
            }
        )
    }

    pub fn is_done(&self) -> bool {
        self.done
    }
}

// Instr is 8 bytes
const _: [(); 8] = [(); size_of::<Instr>()];
#[derive(Debug, Copy, Clone)]
pub enum Instr {
    // Stack manipulation
    Pop,
    Duplicate,
    LoadOffset(i16),
    StoreOffset(i16),

    // Constants
    PushNil(u16),
    PushBool(bool),
    PushInt(u32),
    PushFloat(u32),
    PushString(u32),

    // Arithmetic
    AddInt,
    AddIntReg(i16, i16),
    SubtractInt,
    MultiplyInt,
    MultiplyIntReg(i16, i16),
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
    LessThanIntReg(i16, i16),
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
    EqualString, // TODO: this is O(N). Must use smaller instructions. Or compare character-by-character and save progress in state of Vm

    // Control Flow
    Jump(ProgramCounter),
    JumpIf(ProgramCounter),
    JumpIfFalse(ProgramCounter),
    Call(CallData),
    CallFuncObj,
    CallExtern(u32),
    Return(u32),
    Stop, // used when returning from main function
    HostFunc(u16),
    Panic,

    // Data Structures
    ConstructStruct(u32),
    ConstructArray(u32),
    ConstructVariant { tag: u16 },
    DeconstructStruct,
    DeconstructArray,
    DeconstructVariant,
    GetField(u16),
    GetFieldOffset(u16, i16),
    SetField(u16),
    SetFieldOffset(u16, i16),
    GetIdx,
    SetIdx,
    MakeClosure { func_addr: ProgramCounter },

    ArrayAppend,
    ArrayLength,
    ArrayPop,
    ConcatStrings, // TODO: this is O(N). Must use smaller instructions. Or concat character-by-character and save progress in Vm
    IntToString,
    FloatToString,

    LoadLib,
    LoadForeignFunc,
}

#[derive(Debug, Copy, Clone)]
pub struct CallData(u32);

impl Display for CallData {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "nargs={}, addr={}", self.get_nargs(), self.get_addr())
    }
}

impl CallData {
    const NARGS_NBITS: u32 = 5;
    const NARGS_SHIFT: u32 = 32 - Self::NARGS_NBITS;
    const NARGS_MASK: u32 = 0b11111 << Self::NARGS_SHIFT;
    const ADDR_MASK: u32 = !Self::NARGS_MASK;

    #[inline(always)]
    pub(crate) fn new(nargs: u32, addr: u32) -> Self {
        debug_assert!(addr <= Self::ADDR_MASK);
        let repr = addr | nargs << Self::NARGS_SHIFT;
        CallData(repr)
    }
    #[inline(always)]
    fn get_addr(&self) -> u32 {
        self.0 & Self::ADDR_MASK
    }
    #[inline(always)]
    fn get_nargs(&self) -> u32 {
        self.0 >> Self::NARGS_SHIFT
    }
}

pub trait ValueTrait:
    Copy
    + Clone
    + Debug
    + From<AbraInt>
    + From<AbraFloat>
    + From<bool>
    + From<ProgramCounter>
    + From<HeapReference>
{
    fn make_nil() -> Self;

    fn get_int(&self, vm: &Vm<Self>) -> AbraInt
    where
        Self: Sized;

    fn get_float(&self, vm: &Vm<Self>) -> AbraFloat
    where
        Self: Sized;

    fn get_bool(&self, vm: &Vm<Self>) -> bool
    where
        Self: Sized;

    fn is_heap_ref(&self) -> bool
    where
        Self: Sized;

    fn get_heap_ref(&self, vm: &Vm<Self>, expected_value_kind: ValueKind) -> HeapReference
    where
        Self: Sized;

    fn get_heap_index(&self, vm: &Vm<Self>, expected_value_kind: ValueKind) -> usize
    where
        Self: Sized;

    fn view_string<'a>(&self, vm: &'a Vm<Self>) -> &'a String
    where
        Self: Sized;

    fn get_addr(&self, vm: &Vm<Self>) -> ProgramCounter
    where
        Self: Sized;
}

// PackedValue is 16 bytes
const _: [(); 16] = [(); size_of::<PackedValue>()];
#[derive(Debug, Clone, Copy)]
pub struct PackedValue(u64, /*is_pointer*/ bool);

#[derive(Debug, Clone, Copy)]
pub enum TaggedValue {
    Nil,
    Bool(bool),
    Int(AbraInt),
    Float(AbraFloat),
    FuncAddr(ProgramCounter),
    HeapReference(HeapReference),
}

#[derive(Debug, Copy, Clone)]
pub struct HeapReference(u64);

impl HeapReference {
    const GROUP_BIT: u64 = 1 << 63;
    const INDEX_MASK: u64 = !Self::GROUP_BIT;

    #[inline(always)]
    fn new(index: usize, heap_group: HeapGroup) -> Self {
        debug_assert!(index as u64 <= Self::INDEX_MASK);
        let mut repr = index as u64;
        match heap_group {
            HeapGroup::One => {}
            HeapGroup::Two => {
                repr |= Self::GROUP_BIT;
            }
        }
        HeapReference(repr)
    }
    #[inline(always)]
    fn get_index(&self) -> usize {
        (self.0 & Self::INDEX_MASK) as usize
    }
    #[inline(always)]
    fn get_group(&self) -> HeapGroup {
        if self.0 & Self::GROUP_BIT == 0 {
            HeapGroup::One
        } else {
            HeapGroup::Two
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
enum HeapGroup {
    One,
    Two,
}

impl From<bool> for TaggedValue {
    #[inline(always)]
    fn from(b: bool) -> Self {
        Self::Bool(b)
    }
}

impl From<AbraInt> for TaggedValue {
    #[inline(always)]
    fn from(n: AbraInt) -> Self {
        Self::Int(n)
    }
}

impl From<AbraFloat> for TaggedValue {
    #[inline(always)]
    fn from(n: AbraFloat) -> Self {
        Self::Float(n)
    }
}

impl From<ProgramCounter> for TaggedValue {
    #[inline(always)]
    fn from(n: ProgramCounter) -> Self {
        Self::FuncAddr(n)
    }
}

impl From<HeapReference> for TaggedValue {
    #[inline(always)]
    fn from(n: HeapReference) -> Self {
        Self::HeapReference(n)
    }
}

impl ValueTrait for TaggedValue {
    #[inline(always)]
    fn make_nil() -> Self {
        TaggedValue::Nil
    }

    #[inline(always)]
    fn get_int(&self, vm: &Vm<Self>) -> AbraInt {
        match self {
            TaggedValue::Int(i) => *i,
            _ => vm.fail_wrong_type(ValueKind::Int),
        }
    }

    #[inline(always)]
    fn get_float(&self, vm: &Vm<Self>) -> AbraFloat {
        match self {
            TaggedValue::Float(f) => *f,
            _ => vm.fail_wrong_type(ValueKind::Int),
        }
    }

    #[inline(always)]
    fn get_bool(&self, vm: &Vm<Self>) -> bool {
        match self {
            TaggedValue::Bool(b) => *b,
            _ => vm.fail_wrong_type(ValueKind::Bool),
        }
    }

    #[inline(always)]
    fn is_heap_ref(&self) -> bool {
        matches!(self, TaggedValue::HeapReference(..))
    }

    #[inline(always)]
    fn get_heap_ref(&self, vm: &Vm<Self>, expected_value_kind: ValueKind) -> HeapReference
    where
        Self: Sized,
    {
        match self {
            TaggedValue::HeapReference(r) => *r,
            _ => vm.fail_wrong_type(expected_value_kind),
        }
    }

    #[inline(always)]
    fn get_heap_index(&self, vm: &Vm<Self>, expected_value_kind: ValueKind) -> usize {
        match self {
            TaggedValue::HeapReference(r) => r.get_index(),
            _ => vm.fail_wrong_type(expected_value_kind),
        }
    }

    #[inline(always)]
    fn view_string<'a>(&self, vm: &'a Vm<Self>) -> &'a String {
        let index = self.get_heap_index(vm, ValueKind::String);
        match &vm.heap[index].kind {
            ManagedObjectKind::String(s) => s,
            _ => vm.fail_wrong_type(ValueKind::String),
        }
    }

    #[inline(always)]
    fn get_addr(&self, vm: &Vm<Self>) -> ProgramCounter {
        match self {
            TaggedValue::FuncAddr(addr) => *addr,
            _ => vm.fail_wrong_type(ValueKind::Int),
        }
    }
}

impl From<bool> for PackedValue {
    #[inline(always)]
    fn from(b: bool) -> Self {
        Self(if b { 1 } else { 0 }, false)
    }
}

impl From<AbraInt> for PackedValue {
    #[inline(always)]
    fn from(n: AbraInt) -> Self {
        Self(n as u64, false)
    }
}

impl From<AbraFloat> for PackedValue {
    #[inline(always)]
    fn from(n: AbraFloat) -> Self {
        Self(AbraFloat::to_bits(n), false)
    }
}

impl From<ProgramCounter> for PackedValue {
    #[inline(always)]
    fn from(n: ProgramCounter) -> Self {
        Self(n.0 as u64, false)
    }
}

impl From<HeapReference> for PackedValue {
    #[inline(always)]
    fn from(n: HeapReference) -> Self {
        Self(n.0, true)
    }
}

impl ValueTrait for PackedValue {
    #[inline(always)]
    fn make_nil() -> Self {
        Self(0, false)
    }

    #[inline(always)]
    fn get_int(&self, _vm: &Vm<Self>) -> AbraInt {
        self.0 as AbraInt
    }

    #[inline(always)]
    fn get_float(&self, _vm: &Vm<Self>) -> AbraFloat {
        AbraFloat::from_bits(self.0)
    }

    #[inline(always)]
    fn get_bool(&self, _vm: &Vm<Self>) -> bool {
        self.0 != 0
    }

    #[inline(always)]
    fn is_heap_ref(&self) -> bool {
        self.1
    }

    #[inline(always)]
    fn get_heap_ref(&self, _vm: &Vm<Self>, _expected_value_kind: ValueKind) -> HeapReference
    where
        Self: Sized,
    {
        HeapReference(self.0)
    }

    #[inline(always)]
    fn get_heap_index(&self, _vm: &Vm<Self>, _expected_value_kind: ValueKind) -> usize {
        let heap_ref = HeapReference(self.0);
        heap_ref.get_index()
    }

    #[inline(always)]
    fn view_string<'a>(&self, vm: &'a Vm<Self>) -> &'a String {
        let index = self.get_heap_index(vm, ValueKind::String);
        match &vm.heap[index].kind {
            ManagedObjectKind::String(s) => s,
            _ => vm.fail_wrong_type(ValueKind::String),
        }
    }

    #[inline(always)]
    fn get_addr(&self, _vm: &Vm<Self>) -> ProgramCounter {
        ProgramCounter(self.0 as u32)
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_base: usize,
    nargs: u8,
}

// ReferenceType

#[derive(Debug, Clone)]
struct ManagedObject<Value: ValueTrait> {
    kind: ManagedObjectKind<Value>,

    forwarding_pointer: Cell<Option<usize>>,
}

impl<Value: ValueTrait> ManagedObject<Value> {
    #[inline(always)]
    fn new(kind: ManagedObjectKind<Value>) -> Self {
        Self {
            kind,
            forwarding_pointer: Cell::new(None),
        }
    }
}

#[derive(Debug, Clone)]
enum ManagedObjectKind<Value: ValueTrait> {
    Enum { tag: u16, value: Value },
    DynArray(Vec<Value>),
    Struct(Box<[Value]>),
    String(String),
}

impl<Value: ValueTrait> Vm<Value> {
    pub fn run(&mut self) {
        self.validate();
        while self.step() {}
    }

    pub fn run_n_steps(&mut self, mut steps: u32) {
        self.validate();
        while steps > 0 && self.step() {
            steps -= 1;
        }
    }

    fn validate(&self) {
        if self.pending_host_func.is_some() {
            panic!("must handle pending host func");
        }
        if self.error.is_some() {
            panic!("forgot to check error on vm");
        }
    }

    #[inline(always)]
    fn step(&mut self) -> bool {
        let instr = self.program[self.pc.get()];

        self.pc.0 += 1;
        match instr {
            Instr::PushNil(n) => {
                for _ in 0..n {
                    self.push(Value::make_nil());
                }
            }
            Instr::PushInt(n) => {
                self.push(self.int_constants[n as usize]);
            }
            Instr::PushFloat(f) => {
                self.push(self.float_constants[f as usize]);
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
                self.pop();
            }
            Instr::Duplicate => {
                let v = self.top();
                self.push(*v);
            }
            Instr::LoadOffset(n) => {
                let v = self.load_offset(n);
                self.push(*v);
            }
            Instr::StoreOffset(n) => {
                let idx = self.stack_base.wrapping_add_signed(n as isize);
                let v = self.pop();
                self.value_stack[idx] = v;
            }
            Instr::AddInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a.wrapping_add(b));
            }
            Instr::AddIntReg(reg1, reg2) => {
                let a = self.load_offset(reg1).get_int(self);
                let b = self.load_offset(reg2).get_int(self);
                self.push(a.wrapping_add(b));
            }
            Instr::SubtractInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a.wrapping_sub(b));
            }
            Instr::MultiplyInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a.wrapping_mul(b));
            }
            Instr::MultiplyIntReg(reg1, reg2) => {
                let a = self.load_offset(reg1).get_int(self);
                let b = self.load_offset(reg2).get_int(self);
                self.push(a.wrapping_mul(b));
            }
            Instr::DivideInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                if b == 0 {
                    self.error = Some(Box::new(self.make_error(VmErrorKind::DivisionByZero))); // TODO: why is this boxed
                    return false;
                }
                self.set_top(a.wrapping_div(b));
            }
            Instr::PowerInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a.wrapping_pow(b as u32));
            }
            Instr::Modulo => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a % b);
            }
            Instr::AddFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a + b);
            }
            Instr::SubtractFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a - b);
            }
            Instr::MultiplyFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a * b);
            }
            Instr::DivideFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                if b == 0.0 {
                    self.error = Some(Box::new(self.make_error(VmErrorKind::DivisionByZero))); // TODO: why is this boxed
                    return false;
                }
                self.set_top(a / b);
            }
            Instr::PowerFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a.powf(b));
            }
            Instr::SquareRoot => {
                let a = self.top().get_float(self);
                self.set_top(a.sqrt());
            }
            Instr::Not => {
                let a = self.top().get_bool(self);
                self.set_top(!a);
            }
            Instr::And => {
                let b = self.pop_bool();
                let a = self.top().get_bool(self);
                self.set_top(a && b);
            }
            Instr::Or => {
                let b = self.pop_bool();
                let a = self.top().get_bool(self);
                self.set_top(a || b);
            }
            Instr::LessThanInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a < b);
            }
            Instr::LessThanIntReg(reg1, reg2) => {
                let a = self.load_offset(reg1).get_int(self);
                let b = self.load_offset(reg2).get_int(self);
                self.push(a < b);
            }
            Instr::LessThanOrEqualInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a <= b);
            }
            Instr::GreaterThanInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a > b);
            }
            Instr::GreaterThanOrEqualInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a >= b);
            }
            Instr::LessThanFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a < b);
            }
            Instr::LessThanOrEqualFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a <= b);
            }
            Instr::GreaterThanFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a > b);
            }
            Instr::GreaterThanOrEqualFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a >= b);
            }
            Instr::EqualInt => {
                let b = self.pop_int();
                let a = self.top().get_int(self);
                self.set_top(a == b);
            }
            Instr::EqualFloat => {
                let b = self.pop_float();
                let a = self.top().get_float(self);
                self.set_top(a == b);
            }
            Instr::EqualBool => {
                let b = self.pop_bool();
                let a = self.top().get_bool(self);
                self.set_top(a == b);
            }
            Instr::EqualString => {
                let b = self.pop().view_string(self);
                let a = self.top().view_string(self);
                self.set_top(a == b);
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
            Instr::JumpIfFalse(target) => {
                let v = self.pop_bool();
                if !v {
                    self.pc = target;
                }
            }
            Instr::Call(call_data) => {
                let nargs = call_data.get_nargs();
                let target = call_data.get_addr();
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_base: self.stack_base,
                    nargs: nargs as u8,
                });
                self.pc = ProgramCounter(target);
                self.stack_base = self.value_stack.len();
            }
            Instr::CallFuncObj => {
                let nargs = self.pop_int(); // TODO: put nargs in the instruction itself
                let addr = self.pop_addr();
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_base: self.stack_base,
                    nargs: nargs as u8,
                });

                self.pc = addr;
                self.stack_base = self.value_stack.len();
            }
            Instr::Return(nargs) => {
                if nargs != 0 {
                    // TODO make a separate instruction for when nargs == 0
                    let idx = self.stack_base.wrapping_add_signed(-(nargs as isize));
                    let v = self.top();
                    self.value_stack[idx] = *v;
                }

                let frame = self.call_stack.pop().unwrap();
                self.pc = frame.pc;
                let old_stack_base = self.stack_base;
                self.stack_base = frame.stack_base;
                self.value_stack
                    .truncate(old_stack_base - (frame.nargs as usize) + 1);
            }
            Instr::Stop => {
                self.value_stack.truncate(1);
                self.done = true;
                return false;
            }
            Instr::Panic => {
                let msg = self.pop().view_string(self);
                self.error = Some(Box::new(self.make_error(VmErrorKind::Panic(msg.clone()))));
                return false;
            }
            Instr::ConstructStruct(n) => self.construct_struct(n as usize),
            Instr::ConstructArray(n) => self.construct_array(n as usize),
            Instr::DeconstructStruct => {
                self.deconstruct_struct();
            }
            Instr::DeconstructArray => {
                self.deconstruct_array();
            }
            Instr::DeconstructVariant => {
                self.deconstruct_variant();
            }
            Instr::GetField(index) => {
                let obj = self.top();
                let heap_index = obj.get_heap_index(self, ValueKind::Struct);
                let field = match &self.heap[heap_index].kind {
                    ManagedObjectKind::Struct(fields) => fields[index as usize],
                    _ => self.fail_wrong_type(ValueKind::Struct),
                };
                self.set_top(field);
            }
            Instr::GetFieldOffset(index, offset) => {
                let idx = self.stack_base.wrapping_add_signed(offset as isize); // TODO: don't use wrapping_add_signed, we want it to panic on debug builds
                let obj = self.value_stack[idx];
                let heap_index = obj.get_heap_index(self, ValueKind::Struct);
                let field = match &self.heap[heap_index].kind {
                    ManagedObjectKind::Struct(fields) => fields[index as usize],
                    _ => self.fail_wrong_type(ValueKind::Struct),
                };
                self.push(field);
            }
            Instr::SetField(index) => {
                let obj = self.pop();
                let rvalue = self.pop();
                let heap_index = obj.get_heap_index(self, ValueKind::Struct);
                match &mut self.heap[heap_index].kind {
                    ManagedObjectKind::Struct(fields) => {
                        fields[index as usize] = rvalue;
                    }
                    _ => self.fail_wrong_type(ValueKind::Struct),
                }
            }
            Instr::SetFieldOffset(index, offset) => {
                let idx = self.stack_base.wrapping_add_signed(offset as isize); // TODO: don't use wrapping_add_signed, we want it to panic on debug builds. Same for LoadOffset etc
                let obj = self.value_stack[idx];
                let rvalue = self.pop();
                let heap_index = obj.get_heap_index(self, ValueKind::Struct);
                match &mut self.heap[heap_index].kind {
                    ManagedObjectKind::Struct(fields) => {
                        fields[index as usize] = rvalue;
                    }
                    _ => self.fail_wrong_type(ValueKind::Struct),
                }
            }
            Instr::GetIdx => {
                let obj = self.pop();
                let idx = self.top().get_int(self);
                let heap_index = obj.get_heap_index(self, ValueKind::Array);
                match &self.heap[heap_index].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        if idx as usize >= fields.len() || idx < 0 {
                            self.fail(VmErrorKind::ArrayOutOfBounds);
                        }
                        let field = fields[idx as usize];
                        self.set_top(field);
                    }
                    _ => self.fail_wrong_type(ValueKind::Array),
                }
            }
            Instr::SetIdx => {
                let obj = self.pop();
                let idx = self.pop_int();
                let rvalue = self.pop();
                let heap_index = obj.get_heap_index(self, ValueKind::Array);
                match &mut self.heap[heap_index].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        if idx as usize >= fields.len() || idx < 0 {
                            self.fail(VmErrorKind::ArrayOutOfBounds);
                        }
                        fields[idx as usize] = rvalue;
                    }
                    _ => self.fail_wrong_type(ValueKind::Array),
                }
            }
            Instr::ConstructVariant { tag } => {
                self.construct_variant(tag);
            }
            Instr::MakeClosure { func_addr } => {
                self.value_stack.push(Value::from(func_addr));
            }
            Instr::ArrayAppend => {
                let rvalue = self.pop();
                let obj = self.top();
                let heap_index = obj.get_heap_index(self, ValueKind::Array);
                match &mut self.heap[heap_index].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        fields.push(rvalue);
                    }
                    _ => self.fail_wrong_type(ValueKind::Array),
                }
                self.set_top(Value::make_nil());
            }
            Instr::ArrayLength => {
                let len = self.array_len();
                self.set_top(len as AbraInt);
            }
            Instr::ArrayPop => {
                let obj = self.top();
                let heap_index = obj.get_heap_index(self, ValueKind::Array);
                match &mut self.heap[heap_index].kind {
                    ManagedObjectKind::DynArray(fields) => {
                        let rvalue = fields.pop().expect("array underflow");
                        self.set_top(rvalue);
                    }
                    _ => self.fail_wrong_type(ValueKind::Array),
                }
            }
            Instr::ConcatStrings => {
                let b = self.pop();
                let a = self.top();
                let a_str = a.view_string(self);
                let b_str = b.view_string(self);
                let mut new_str = String::with_capacity(a_str.len() + b_str.len());
                new_str.push_str(a_str);
                new_str.push_str(b_str);
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(new_str)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.set_top(r);
            }
            Instr::IntToString => {
                let n = self.top().get_int(self);
                let s = n.to_string();
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.set_top(r);
            }
            Instr::FloatToString => {
                let f = self.top().get_float(self);
                let s = f.to_string();
                self.heap
                    .push(ManagedObject::new(ManagedObjectKind::String(s)));
                let r = self.heap_reference(self.heap.len() - 1);
                self.set_top(r);
            }
            Instr::HostFunc(eff) => {
                self.pending_host_func = Some(eff);
                return false;
            }
            Instr::LoadLib => {
                if cfg!(not(feature = "ffi")) {
                    self.fail(VmErrorKind::FfiNotEnabled);
                }

                #[cfg(feature = "ffi")]
                {
                    // pop libname from stack
                    // load the library with a certain name and add it to the Vm's Vec of libs
                    let libname = self.pop().view_string(self);
                    let lib = unsafe { Library::new(libname) };
                    let Ok(lib) = lib else {
                        self.fail(VmErrorKind::LibLoadFailure(libname.clone()))
                    };
                    self.libs.push(lib);
                }
            }
            Instr::LoadForeignFunc => {
                if cfg!(not(feature = "ffi")) {
                    self.fail(VmErrorKind::FfiNotEnabled);
                }

                #[cfg(feature = "ffi")]
                {
                    // pop foreign func name from stack
                    // load symbol from the last library loaded
                    let symbol_name = self.pop().view_string(self);
                    let lib = self.libs.last().expect("no libraries have been loaded");
                    let symbol /*: Result<libloading::Symbol<unsafe extern "C" fn(*mut Vm) -> ()>, _>*/ =
                        unsafe { lib.get(symbol_name.as_bytes()) };
                    let Ok(symbol) = symbol else {
                        self.fail(VmErrorKind::SymbolLoadFailure(symbol_name.clone()));
                    };
                    self.foreign_functions.push(*symbol);
                }
            }
            Instr::CallExtern(_func_id) => {
                if cfg!(not(feature = "ffi")) {
                    self.fail(VmErrorKind::FfiNotEnabled);
                }

                #[cfg(feature = "ffi")]
                {
                    unsafe {
                        let vm_ptr = self as *mut Vm<Value> as *mut c_void;
                        let abra_vm_functions_ptr = &ABRA_VM_FUNCS as *const AbraVmFunctions;
                        self.foreign_functions[_func_id as usize](vm_ptr, abra_vm_functions_ptr);
                    };
                }
            }
        }
        true
    }

    fn pc_to_error_location(&self, pc: ProgramCounter) -> VmErrorLocation {
        let file_id = match self
            .filename_table
            .binary_search_by_key(&(pc.0), |pair| pair.0)
        {
            Ok(idx) | Err(idx) => {
                let idx = if idx >= 1 { idx - 1 } else { idx };
                self.filename_table[idx].1
            }
        };

        let lineno = match self
            .lineno_table
            .binary_search_by_key(&(pc.0), |pair| pair.0)
        {
            Ok(idx) | Err(idx) => {
                let idx = if idx >= 1 { idx - 1 } else { idx };
                self.lineno_table[idx].1
            }
        };

        let function_name_id = match self
            .function_name_table
            .binary_search_by_key(&(pc.0), |pair| pair.0)
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

    #[inline(always)]
    fn make_stack_trace(&self) -> Vec<VmErrorLocation> {
        let mut ret = vec![];
        for frame in &self.call_stack {
            ret.push(self.pc_to_error_location(frame.pc));
        }
        ret
    }

    #[inline(always)]
    fn heap_reference(&mut self, idx: usize) -> Value {
        Value::from(HeapReference::new(idx, self.heap_group))
    }

    pub fn compact(&mut self) {
        self.value_stack.shrink_to_fit();
        self.call_stack.shrink_to_fit();
    }

    pub fn nbytes(&self) -> usize {
        let mut n = self.program.len() * size_of::<Instr>()
            + self.value_stack.len() * size_of::<Value>()
            + self.call_stack.len() * size_of::<CallFrame>()
            + self.heap.len() * size_of::<ManagedObject<Value>>();

        n += self.static_strings.iter().map(|s| s.len()).sum::<usize>();
        n
    }

    pub fn heap_size(&self) -> usize {
        self.heap.len() * size_of::<ManagedObject<Value>>()
    }

    pub fn gc(&mut self) {
        let mut new_heap = Vec::<ManagedObject<Value>>::new();
        let new_heap_group = match self.heap_group {
            HeapGroup::One => HeapGroup::Two,
            HeapGroup::Two => HeapGroup::One,
        };

        // roots
        for i in 0..self.value_stack.len() {
            let v = &self.value_stack[i];
            if v.is_heap_ref() {
                let r = v.get_heap_ref(self, ValueKind::HeapObject);
                let v = &mut self.value_stack[i];
                *v = Value::from(forward(r, &self.heap, 0, &mut new_heap, new_heap_group));
            }
        }

        let mut i = 0;
        while i < new_heap.len() {
            let new_heap_len = new_heap.len();
            let obj = &mut new_heap[i];
            let mut to_add: Vec<ManagedObject<Value>> = vec![];
            match &mut obj.kind {
                ManagedObjectKind::DynArray(fields) => {
                    for v in fields {
                        if v.is_heap_ref() {
                            let r = v.get_heap_ref(self, ValueKind::HeapObject);
                            *v = Value::from(forward(
                                r,
                                &self.heap,
                                new_heap_len,
                                &mut to_add,
                                new_heap_group,
                            ));
                        }
                    }
                }
                ManagedObjectKind::Struct(fields) => {
                    // TODO: code duplication
                    for v in fields {
                        if v.is_heap_ref() {
                            let r = v.get_heap_ref(self, ValueKind::HeapObject);
                            *v = Value::from(forward(
                                r,
                                &self.heap,
                                new_heap_len,
                                &mut to_add,
                                new_heap_group,
                            ));
                        }
                    }
                }
                ManagedObjectKind::Enum { tag: _, value: v } => {
                    if v.is_heap_ref() {
                        let r = v.get_heap_ref(self, ValueKind::HeapObject);
                        *v = Value::from(forward(
                            r,
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

    #[inline(always)]
    fn push(&mut self, x: impl Into<Value>) {
        self.value_stack.push(x.into());
    }

    #[inline(always)]
    pub fn pop_int(&mut self) -> AbraInt {
        self.pop().get_int(self)
    }

    #[inline(always)]
    pub fn pop_float(&mut self) -> AbraFloat {
        self.pop().get_float(self)
    }

    #[inline(always)]
    fn pop_addr(&mut self) -> ProgramCounter {
        self.pop().get_addr(self)
    }

    #[inline(always)]
    pub(crate) fn pop_bool(&mut self) -> bool {
        self.pop().get_bool(self)
    }
}

fn forward<Value: ValueTrait>(
    r: HeapReference,
    old_heap: &[ManagedObject<Value>],
    new_heap_len: usize,
    to_add: &mut Vec<ManagedObject<Value>>,
    new_heap_group: HeapGroup,
) -> HeapReference {
    if r.get_group() != new_heap_group {
        // from space
        let old_obj = &old_heap[r.get_index()];
        match old_obj.forwarding_pointer.get() {
            Some(f) => {
                // return f
                HeapReference::new(f, new_heap_group)
            }
            None => {
                // copy to new heap and install forwarding pointer in old heap object
                let new_idx = to_add.len() + new_heap_len;

                let new_obj = old_obj.clone();
                new_obj.forwarding_pointer.replace(None);
                to_add.push(new_obj);

                old_obj.forwarding_pointer.replace(Some(new_idx));

                HeapReference::new(new_idx, new_heap_group)
            }
        }
    } else {
        // to space
        // this reference already points to the new heap
        r
    }
}

impl<Value: ValueTrait> Debug for Vm<Value> {
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
