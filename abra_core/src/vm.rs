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
use std::alloc::{Layout, alloc, dealloc};
use std::cmp::PartialEq;
use std::error::Error;
#[cfg(feature = "ffi")]
use std::ffi::c_void;
use std::fmt::Debug;
use std::ptr::null_mut;
use std::{
    fmt::{Display, Formatter},
    mem, ptr,
};

pub struct Vm {
    program: Vec<Instr>,
    pc: ProgramCounter,
    // stack
    stack_base: usize,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    // heap
    heaplist: Vec<*mut ObjectHeader>,
    gray_stack: Vec<*mut ObjectHeader>,
    gc_state: GcState,
    // constants
    int_constants: Vec<i64>,
    float_constants: Vec<f64>,
    static_strings: Vec<String>,
    filename_arena: Vec<String>,
    function_name_arena: Vec<String>,
    // source map
    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,
    // status
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
            value_stack: vec![().into()],
            call_stack: Vec::new(),
            heaplist: vec![],
            gray_stack: vec![],
            gc_state: GcState::Idle,

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

impl Vm {
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
    pub fn top(&self) -> Value {
        match self.value_stack.last() {
            Some(v) => *v,
            None => panic!("stack is empty"),
        }
    }

    #[inline(always)]
    fn set_top(&mut self, val: impl Into<Value>) {
        let len = self.value_stack.len();
        self.value_stack[len - 1] = val.into();
    }

    #[inline(always)]
    pub fn load_offset(&self, offset: i16) -> Value {
        self.value_stack[self.stack_base.wrapping_add_signed(offset as isize)]
    }

    #[inline(always)]
    pub fn store_offset(&mut self, offset: i16, v: impl Into<Value>) {
        self.value_stack[self.stack_base.wrapping_add_signed(offset as isize)] = v.into();
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
        let s = StringObject::new(s, self);
        let r = Value::from(s);
        self.push(r);
    }

    #[inline(always)]
    pub fn push_nil(&mut self) {
        self.push(());
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
        let variant = EnumObject::new(tag, value, self);
        let r = Value::from(variant);
        self.set_top(r);
    }

    #[inline(always)]
    pub fn construct_tuple(&mut self, n: usize) {
        self.construct_struct(n)
    }

    #[inline(always)]
    pub fn construct_struct(&mut self, n: usize) {
        let fields = self.pop_n(n);
        let ptr = StructObject::new(fields, self);
        self.push(ptr);
    }

    #[inline(always)]
    pub fn construct_array(&mut self, n: usize) {
        let fields = self.pop_n(n);
        let ptr = ArrayObject::new(fields, self);
        self.push(ptr);
    }

    #[inline(always)]
    pub fn deconstruct_struct(&mut self) {
        let val = self.pop();
        let s = val.get_struct(self);
        let fields = s.get_fields();
        self.value_stack.extend(fields.iter().rev());
    }

    #[inline(always)]
    pub fn deconstruct_array(&mut self) {
        let val = self.pop();
        let arr = val.get_array(self);
        self.value_stack.extend(arr.elems.iter().rev());
    }

    #[inline(always)]
    pub fn deconstruct_variant(&mut self) {
        let val = self.top();
        let (val, tag) = {
            let variant = val.get_variant(self);
            (variant.val, variant.tag)
        };
        self.set_top(val);
        self.push(tag as AbraInt);
    }

    #[inline(always)]
    pub fn array_len(&mut self) -> usize {
        let val = self.top();
        let arr = val.get_array(self);
        arr.elems.len()
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
    IncrementRegImm(i16, i16),
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
    CallFuncObj(u32),
    CallExtern(u32),
    Return(u32),
    Stop, // used when returning from main function
    HostFunc(u16),
    Panic,

    // Data Structures
    ConstructStruct(u32),
    ConstructArray(u32),
    // TODO: it's a shame that simple enums like Red | Blue | Green aren't just represented as an int.
    // TODO: there should be two types of enums: primitive and object enums. Primitive enums are basically just ints and don't require allocations
    // TODO: pattern matching with primitive enums should also be much much faster, equivalent to a switch.
    ConstructVariant { tag: u16 },
    DeconstructStruct,
    DeconstructArray,
    DeconstructVariant,
    GetField(u16),
    GetFieldOffset(u16, i16),
    SetField(u16),
    SetFieldOffset(u16, i16),
    GetIdx,
    GetIdxOffset(i16, i16),
    SetIdx,
    SetIdxOffset(i16, i16),
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

// PackedValue is 16 bytes currently
const _: [(); 16] = [(); size_of::<Value>()];
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value(u64, /*is_pointer*/ bool);
// TODO: get rid of is_pointer using separate bitvec

impl Value {
    #[inline(always)]
    pub fn get_int(&self, _vm: &Vm) -> AbraInt {
        self.0 as AbraInt
    }

    #[inline(always)]
    pub fn get_float(&self, _vm: &Vm) -> AbraFloat {
        AbraFloat::from_bits(self.0)
    }

    #[inline(always)]
    pub fn get_bool(&self, _vm: &Vm) -> bool {
        self.0 != 0
    }

    #[inline(always)]
    unsafe fn get_object_header<'a>(&self) -> &'a mut ObjectHeader {
        unsafe { &mut *(self.0 as *mut ObjectHeader) }
    }

    #[inline(always)]
    fn get_struct<'a>(&self, _vm: &mut Vm) -> &'a StructObject {
        unsafe { &*(self.0 as *const StructObject) }
    }

    #[inline(always)]
    unsafe fn get_struct_mut<'a>(&self, _vm: &mut Vm) -> &'a mut StructObject {
        unsafe { &mut *(self.0 as *mut StructObject) }
    }

    #[inline(always)]
    fn get_array<'a>(&self, _vm: &mut Vm) -> &'a ArrayObject
    where
        Self: Sized,
    {
        unsafe { &*(self.0 as *const ArrayObject) }
    }

    #[inline(always)]
    unsafe fn get_array_mut<'a>(&self, _vm: &mut Vm) -> &'a mut ArrayObject
    where
        Self: Sized,
    {
        unsafe { &mut *(self.0 as *mut ArrayObject) }
    }

    #[inline(always)]
    fn get_variant<'a>(&self, _vm: &Vm) -> &'a EnumObject
    where
        Self: Sized,
    {
        unsafe { &mut *(self.0 as *mut EnumObject) }
    }

    #[inline(always)]
    pub fn view_string<'a>(&self, _vm: &Vm) -> &'a String {
        let so = unsafe { &*(self.0 as *const StringObject) };
        &so.str
    }

    #[inline(always)]
    fn get_addr(&self, _vm: &Vm) -> ProgramCounter {
        ProgramCounter(self.0 as u32)
    }
}

impl From<()> for Value {
    #[inline(always)]
    fn from(_: ()) -> Self {
        Self(0, false)
    }
}

impl From<bool> for Value {
    #[inline(always)]
    fn from(b: bool) -> Self {
        Self(if b { 1 } else { 0 }, false)
    }
}

impl From<AbraInt> for Value {
    #[inline(always)]
    fn from(n: AbraInt) -> Self {
        Self(n as u64, false)
    }
}

impl From<AbraFloat> for Value {
    #[inline(always)]
    fn from(n: AbraFloat) -> Self {
        Self(AbraFloat::to_bits(n), false)
    }
}

impl From<ProgramCounter> for Value {
    #[inline(always)]
    fn from(n: ProgramCounter) -> Self {
        Self(n.0 as u64, false)
    }
}

impl From<*mut ArrayObject> for Value {
    #[inline(always)]
    fn from(ptr: *mut ArrayObject) -> Self {
        Self(ptr as u64, true)
    }
}

impl From<*mut StructObject> for Value {
    #[inline(always)]
    fn from(ptr: *mut StructObject) -> Self {
        Self(ptr as u64, true)
    }
}

impl From<*mut EnumObject> for Value {
    #[inline(always)]
    fn from(ptr: *mut EnumObject) -> Self {
        Self(ptr as u64, true)
    }
}

impl From<*mut StringObject> for Value {
    #[inline(always)]
    fn from(ptr: *mut StringObject) -> Self {
        Self(ptr as u64, true)
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_base: usize,
    nargs: u8,
}

// NEW reference types

#[derive(PartialEq, Eq)]
enum GcState {
    Idle,
    Marking,
    Sweeping { index: usize },
}

#[repr(C)]
struct ObjectHeader {
    kind: ObjectKind,
    color: Color,
}

impl ObjectHeader {
    unsafe fn dealloc(&mut self) {
        let kind = self.kind;
        match kind {
            ObjectKind::String => {
                let obj = unsafe { self as *mut Self as *mut StringObject };
                let _ = unsafe { Box::from_raw(obj) };
            }
            ObjectKind::Enum => {
                let obj = unsafe { self as *mut Self as *mut EnumObject };
                let _ = unsafe { Box::from_raw(obj) };
            }
            ObjectKind::Struct => {
                let obj = unsafe { &*(self as *mut Self as *mut StructObject) };
                let layout = obj.layout();
                unsafe { dealloc(self as *mut ObjectHeader as *mut u8, layout) };
            }
            ObjectKind::Array => {
                let obj = unsafe { self as *mut Self as *mut ArrayObject };
                let _ = unsafe { Box::from_raw(obj) };
            }
        }
    }
}

#[derive(Copy, Clone)]
#[repr(C)]
enum ObjectKind {
    Enum,
    Array,
    Struct,
    String,
}

#[derive(PartialEq, Eq)]
#[repr(u8)]
enum Color {
    White,
    Gray,
    Black,
}

#[repr(C)]
struct StructObject {
    header: ObjectHeader,
    len: usize,
    // data: [PackedValue],
}

impl StructObject {
    fn new(data: Vec<Value>, vm: &mut Vm) -> *mut StructObject {
        let len = data.len();
        let layout = Self::layout_helper(len);
        let prefix_size = size_of::<StructObject>();

        unsafe {
            let raw = alloc(layout);
            if raw.is_null() {
                std::alloc::handle_alloc_error(layout);
            }

            let obj = raw as *mut StructObject;
            ptr::write(
                obj,
                StructObject {
                    header: ObjectHeader {
                        kind: ObjectKind::Struct,
                        color: match &vm.gc_state {
                            GcState::Idle => Color::White,
                            GcState::Marking => Color::Gray,
                            GcState::Sweeping { .. } => Color::Black,
                        },
                    },
                    len,
                },
            );

            let base = raw.add(prefix_size) as *mut Value;
            let src = data.as_ptr();

            for i in 0..len {
                ptr::write(base.add(i), ptr::read(src.add(i)));
            }

            vm.heaplist.push(obj as *mut ObjectHeader);
            if vm.gc_state == GcState::Marking {
                vm.gray_stack.push(obj as *mut ObjectHeader);
            }

            obj
        }
    }

    fn header_ptr(self: &mut StructObject) -> *mut ObjectHeader {
        self as *mut Self as *mut ObjectHeader
    }

    fn layout(&self) -> Layout {
        Self::layout_helper(self.len)
    }

    fn layout_helper(len: usize) -> Layout {
        let len = len;

        let prefix_size = size_of::<StructObject>();
        let value_size = size_of::<Value>();
        let align = align_of::<StructObject>().max(align_of::<Value>());

        let total_size = prefix_size + len * value_size;
        Layout::from_size_align(total_size, align).unwrap()
    }

    fn get_fields(&self) -> &[Value] {
        unsafe { std::slice::from_raw_parts(self.data_ptr(), self.len) }
    }

    fn get_fields_mut(&mut self) -> &mut [Value] {
        unsafe { std::slice::from_raw_parts_mut(self.data_ptr(), self.len) }
    }

    fn data_ptr(&self) -> *mut Value {
        unsafe {
            (self as *const StructObject as *mut u8).add(size_of::<StructObject>()) as *mut Value
        }
    }
}

#[repr(C)]
struct ArrayObject {
    header: ObjectHeader,
    elems: Vec<Value>,
}

impl ArrayObject {
    fn new(data: Vec<Value>, vm: &mut Vm) -> *mut ArrayObject {
        let header = ObjectHeader {
            kind: ObjectKind::Array,
            color: match &vm.gc_state {
                GcState::Idle => Color::White,
                GcState::Marking => Color::Gray,
                GcState::Sweeping { .. } => Color::Black,
            },
        };
        let b = Box::new(ArrayObject {
            header,
            elems: data,
        });
        let ptr = Box::leak(b);
        vm.heaplist
            .push(ptr as *mut ArrayObject as *mut ObjectHeader);
        if vm.gc_state == GcState::Marking {
            vm.gray_stack
                .push(ptr as *mut ArrayObject as *mut ObjectHeader);
        }
        ptr
    }

    fn header_ptr(self: &mut Self) -> *mut ObjectHeader {
        self as *mut Self as *mut ObjectHeader
    }
}

#[repr(C)]
struct EnumObject {
    header: ObjectHeader,
    tag: u16,
    val: Value,
}

impl EnumObject {
    fn new(tag: u16, val: Value, vm: &mut Vm) -> *mut EnumObject {
        let header = ObjectHeader {
            kind: ObjectKind::Enum,
            color: match &vm.gc_state {
                GcState::Idle => Color::White,
                GcState::Marking => Color::Gray,
                GcState::Sweeping { .. } => Color::Black,
            },
        };
        let b = Box::new(EnumObject { header, tag, val });
        let ptr = Box::leak(b);
        vm.heaplist
            .push(ptr as *mut EnumObject as *mut ObjectHeader);
        if vm.gc_state == GcState::Marking {
            vm.gray_stack
                .push(ptr as *mut EnumObject as *mut ObjectHeader);
        }
        ptr
    }

    fn header_ptr(self: &mut Self) -> *mut ObjectHeader {
        self as *mut Self as *mut ObjectHeader
    }
}

#[repr(C)]
struct StringObject {
    header: ObjectHeader,
    str: String, // TODO: inline the string's contents. Make helper functions for writing to the end of string.
}

impl StringObject {
    fn new(str: String, vm: &mut Vm) -> *mut StringObject {
        let header = ObjectHeader {
            kind: ObjectKind::String,
            color: match &vm.gc_state {
                GcState::Idle => Color::White,
                GcState::Marking => Color::Gray,
                GcState::Sweeping { .. } => Color::Black,
            },
        };
        let b = Box::new(StringObject { header, str });
        let ptr = Box::leak(b);
        vm.heaplist
            .push(ptr as *mut StringObject as *mut ObjectHeader);
        if vm.gc_state == GcState::Marking {
            vm.gray_stack
                .push(ptr as *mut StringObject as *mut ObjectHeader);
        }
        ptr
    }

    fn header_ptr(self: &mut Self) -> *mut ObjectHeader {
        self as *mut Self as *mut ObjectHeader
    }
}

impl Vm {
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
        self.maybe_gc(); // TODO: is it bad to run this every step...?
        let instr = self.program[self.pc.get()];

        self.pc.0 += 1;
        match instr {
            Instr::PushNil(n) => {
                for _ in 0..n {
                    self.push(());
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
                // TODO: copying string every time is not good ...
                let s = &self.static_strings[idx as usize];
                let s = StringObject::new(s.clone(), self);
                self.push(s);
            }
            Instr::Pop => {
                self.pop();
            }
            Instr::Duplicate => {
                let v = self.top();
                self.push(v);
            }
            Instr::LoadOffset(n) => {
                let v = self.load_offset(n);
                self.push(v);
            }
            Instr::StoreOffset(n) => {
                let v = self.pop();
                self.store_offset(n, v);
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
            Instr::IncrementRegImm(reg, n) => {
                let a = self.load_offset(reg).get_int(self);
                self.store_offset(reg, a.wrapping_add(n as i64));
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
                    self.error = Some(self.make_error(VmErrorKind::DivisionByZero).into());
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
                    self.error = Some(self.make_error(VmErrorKind::DivisionByZero).into());
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
            Instr::CallFuncObj(nargs) => {
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
                let idx = self.stack_base.wrapping_add_signed(-(nargs as isize));
                let v = self.top();
                self.value_stack[idx] = v;

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
                let val = self.top();
                let s = val.get_struct(self);
                let field = s.get_fields()[index as usize];
                self.set_top(field);
            }
            Instr::GetFieldOffset(index, offset) => {
                let val = self.load_offset(offset);
                let s = val.get_struct(self);
                let field = s.get_fields()[index as usize];
                self.push(field);
            }
            Instr::SetField(index) => {
                let val = self.pop();
                let rvalue = self.pop();
                let s = unsafe { val.get_struct_mut(self) };

                self.write_barrier(s.header_ptr(), rvalue);
                unsafe {
                    s.get_fields_mut()[index as usize] = rvalue;
                }
            }
            Instr::SetFieldOffset(index, offset) => {
                let val = self.load_offset(offset);
                let rvalue = self.pop();
                let s = unsafe { val.get_struct_mut(self) };

                self.write_barrier(s.header_ptr(), rvalue);
                unsafe {
                    s.get_fields_mut()[index as usize] = rvalue;
                }
            }
            Instr::GetIdx => {
                let val = self.pop();
                let idx = self.top().get_int(self);
                let arr = val.get_array(self);
                if idx as usize >= arr.elems.len() || idx < 0 {
                    self.fail(VmErrorKind::ArrayOutOfBounds);
                }
                let field = arr.elems[idx as usize];
                self.set_top(field);
            }
            Instr::GetIdxOffset(reg1, reg2) => {
                let val = self.load_offset(reg2);
                let idx = self.load_offset(reg1).get_int(self);
                let arr = val.get_array(self);
                if idx as usize >= arr.elems.len() || idx < 0 {
                    self.fail(VmErrorKind::ArrayOutOfBounds);
                }
                let field = arr.elems[idx as usize];
                self.push(field);
            }
            Instr::SetIdx => {
                let val = self.pop();
                let idx = self.pop_int();
                let rvalue = self.pop();
                let arr = unsafe { val.get_array_mut(self) };
                if idx as usize >= arr.elems.len() || idx < 0 {
                    self.fail(VmErrorKind::ArrayOutOfBounds);
                }
                self.write_barrier(arr.header_ptr(), rvalue);
                arr.elems[idx as usize] = rvalue;
            }
            Instr::SetIdxOffset(reg1, reg2) => {
                let val = self.load_offset(reg2);
                let idx = self.load_offset(reg1).get_int(self);
                let rvalue = self.pop();
                let arr = unsafe { val.get_array_mut(self) };
                if idx as usize >= arr.elems.len() || idx < 0 {
                    self.fail(VmErrorKind::ArrayOutOfBounds);
                }
                self.write_barrier(arr.header_ptr(), rvalue);
                arr.elems[idx as usize] = rvalue;
            }
            Instr::ConstructVariant { tag } => {
                self.construct_variant(tag);
            }
            Instr::MakeClosure { func_addr } => {
                self.push(func_addr);
            }
            Instr::ArrayAppend => {
                let rvalue = self.pop();
                let val = self.top();
                let arr = unsafe { val.get_array_mut(self) };
                self.write_barrier(arr.header_ptr(), rvalue);
                arr.elems.push(rvalue);
                self.set_top(());
            }
            Instr::ArrayLength => {
                let len = self.array_len();
                self.set_top(len as AbraInt);
            }
            Instr::ArrayPop => {
                let val = self.top();
                let arr = unsafe { val.get_array_mut(self) };
                let lvalue = arr.elems.pop().unwrap();
                self.set_top(lvalue);
            }
            // TODO: it would be better if ConcatString operation extended the LHS with the RHS. Would have to modify how format_append and & work
            // Perhaps LHS of & operator should be some sort of "StringBuilder". Though this is suspiciously similar to cout in C++
            Instr::ConcatStrings => {
                let b = self.pop();
                let a = self.top();
                let a_str = a.view_string(self);
                let b_str = b.view_string(self);
                let mut new_str = String::with_capacity(a_str.len() + b_str.len());
                new_str.push_str(a_str);
                new_str.push_str(b_str);
                let s = StringObject::new(new_str, self);
                let r = Value::from(s);
                self.set_top(r);
            }
            Instr::IntToString => {
                let n = self.top().get_int(self);
                let s = n.to_string();
                let s = StringObject::new(s, self);
                let r = Value::from(s);
                self.set_top(r);
            }
            Instr::FloatToString => {
                let f = self.top().get_float(self);
                let s = f.to_string();
                let s = StringObject::new(s, self);
                let r = Value::from(s);
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
                        let vm_ptr = self as *mut Vm as *mut c_void;
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

    // GARBAGE COLLECTION

    fn maybe_gc(&mut self) {
        match self.gc_state {
            GcState::Idle => {
                const THRESHOLD: usize = 0; // TODO: pick something better
                if self.heaplist.len() > THRESHOLD {
                    self.start_mark_phase();
                }
            }
            GcState::Marking => {
                // process a few gray nodes
                const GC_MARK_SLICE: usize = 4; // TODO: why 4?
                for _ in 0..GC_MARK_SLICE {
                    self.process_gray();
                    if self.gray_stack.is_empty() {
                        self.gc_state = GcState::Sweeping { index: 0 };
                        break;
                    }
                }
            }
            GcState::Sweeping { .. } => {
                const GC_SWEEP_SLICE: usize = 8; // TODO: why 8?
                self.sweep(GC_SWEEP_SLICE);
            }
        }
    }

    fn start_mark_phase(&mut self) {
        // all objects start white
        for header_ptr in &self.heaplist {
            let header = unsafe { &mut **header_ptr };
            header.color = Color::White;
        }

        // mark roots gray
        for v in self.value_stack.iter().cloned() {
            Self::mark(v, &mut self.gray_stack);
        }

        self.gc_state = GcState::Marking;
    }

    fn mark(v: Value, gray_stack: &mut Vec<*mut ObjectHeader>) {
        // if v is not a pointer
        if !v.1 {
            return;
        }

        let header = unsafe { v.get_object_header() };
        if header.color != Color::White {
            return;
        }

        header.color = Color::Gray;
        gray_stack.push(header)
    }

    fn process_gray(&mut self) {
        while let Some(header_ptr) = self.gray_stack.pop() {
            {
                let header = unsafe { &mut *header_ptr };
                header.color = Color::Black;
            }

            let kind = {
                let header = unsafe { &mut *header_ptr };
                header.kind
            };

            match kind {
                ObjectKind::String => {}
                ObjectKind::Enum => {
                    let obj = unsafe { &*(header_ptr as *const EnumObject) };
                    Self::mark(obj.val, &mut self.gray_stack);
                }
                ObjectKind::Struct => {
                    let obj = unsafe { &*(header_ptr as *const StructObject) };
                    for field in obj.get_fields() {
                        Self::mark(*field, &mut self.gray_stack);
                    }
                }
                ObjectKind::Array => {
                    let obj = unsafe { &*(header_ptr as *const ArrayObject) };
                    for elem in &obj.elems {
                        Self::mark(*elem, &mut self.gray_stack);
                    }
                }
            }
        }
    }

    fn write_barrier(&mut self, parent: impl Into<*mut ObjectHeader>, child: Value) {
        if self.gc_state != GcState::Marking {
            return;
        }
        // if child is not a pointer
        if !child.1 {
            return;
        }

        let parent: *mut ObjectHeader = parent.into();
        let parent = unsafe { &mut *parent };
        if parent.color == Color::Black {
            let header = unsafe { child.get_object_header() };
            if header.color == Color::White {
                header.color = Color::Gray;
                self.gray_stack.push(header);
            }
        }
    }

    fn sweep(&mut self, batch: usize) -> bool {
        if let GcState::Sweeping { index } = &mut self.gc_state {
            let len = self.heaplist.len();
            let end = (*index + batch).min(len);

            for i in *index..end {
                let header_ptr = self.heaplist[i];
                let header = unsafe { &mut *header_ptr };
                if header.color == Color::White {
                    unsafe { header.dealloc() };
                    self.heaplist[i] = null_mut();
                } else {
                    header.color = Color::White;
                }
            }

            *index = end;
            if end == len {
                self.gc_state = GcState::Idle;
                self.heaplist.retain(|x| !x.is_null());
                return false;
            }
            return true;
        }
        false
    }

    pub fn compact(&mut self) {
        self.value_stack.shrink_to_fit();
        self.call_stack.shrink_to_fit();
    }

    pub fn nbytes(&self) -> usize {
        let mut n = self.program.len() * size_of::<Instr>()
            + self.value_stack.len() * size_of::<Value>()
            + self.call_stack.len() * size_of::<CallFrame>();
        // TODO: must incorporate heap into calculation;

        n += self.static_strings.iter().map(|s| s.len()).sum::<usize>();
        n
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

impl Debug for Vm {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.debug_struct("Vm")
            .field("pc", &self.pc)
            .field("stack_base", &self.stack_base)
            .field("value_stack", &format!("{:?}", self.value_stack))
            .field("call_stack", &format!("{:?}", self.call_stack))
            // .field("heap", &format!("{:?}", self.heap))
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
