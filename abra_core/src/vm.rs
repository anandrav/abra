/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

#[cfg(feature = "ffi")]
use crate::foreign_bindings::ABRA_VM_FUNCS;
#[cfg(feature = "ffi")]
use crate::foreign_bindings::AbraVmFunctions;
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
use std::{
    fmt::{Display, Formatter},
    ptr,
};

pub type AbraInt = i64;
pub type AbraFloat = f64;

const GC_PAUSE_FACTOR: usize = 2;
const GC_STEP_FACTOR: usize = 2;

pub struct Vm {
    program: Vec<Instr>,
    pc: ProgramCounter,
    // stack
    stack_base: usize,
    value_stack: Vec<Value>,
    call_stack: Vec<CallFrame>,
    // heap
    heap_list: Vec<*mut ObjectHeader>,
    gray_stack: Vec<*mut ObjectHeader>,
    gc_state: GcState,
    gc_visited: bool,
    heap_size: usize,
    gc_debt: usize,
    last_gc_heap_size: usize,
    // constants
    int_constants: Vec<AbraInt>,
    float_constants: Vec<f64>,
    static_strings: Vec<*mut StringObject>,
    // source map
    filename_table: Vec<(BytecodeIndex, u32)>,
    lineno_table: Vec<(BytecodeIndex, u32)>,
    function_name_table: Vec<(BytecodeIndex, u32)>,
    filename_arena: Vec<String>,
    function_name_arena: Vec<String>,
    // status
    pending_host_func: Option<u16>,
    error: Option<Box<VmError>>,
    done: bool,
    // string op state
    string_op_index1: usize,
    string_op_index2: usize,
    string_operand1: Value,
    string_operand2: Value,
    concat_string_builder: Vec<u8>,

    // FFI
    #[cfg(feature = "ffi")]
    libs: Vec<Library>,
    #[cfg(feature = "ffi")]
    foreign_functions: Vec<unsafe extern "C" fn(*mut c_void, *const AbraVmFunctions) -> ()>,
}

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
        let mut vm = Self {
            program: program.instructions,
            pc: ProgramCounter(0),
            stack_base: 0,
            value_stack: vec![],
            call_stack: Vec::new(),
            heap_list: vec![],
            gray_stack: vec![],
            gc_state: GcState::Idle,
            gc_visited: true,
            heap_size: 0,
            gc_debt: 0,
            last_gc_heap_size: 0,

            int_constants: program.int_constants.into_iter().collect(),
            float_constants: program.float_constants.into_iter().collect(),
            static_strings: vec![],
            filename_arena: program.filename_arena.into_iter().collect(),
            function_name_arena: program.function_name_arena.into_iter().collect(),

            filename_table: program.filename_table,
            lineno_table: program.lineno_table,
            function_name_table: program.function_name_table,

            pending_host_func: None,
            error: None,
            done: false,

            string_op_index1: 0,
            string_op_index2: 0,
            string_operand1: Value::from(0),
            string_operand2: Value::from(0),
            concat_string_builder: vec![],

            #[cfg(feature = "ffi")]
            libs: Vec::new(),
            #[cfg(feature = "ffi")]
            foreign_functions: Vec::new(),
        };

        for s in program.static_strings {
            let s_obj = StringObject::new(s, &mut vm);
            vm.static_strings.push(s_obj);
        }

        vm
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

    pub fn top(&self) -> Value {
        match self.value_stack.last() {
            Some(v) => *v,
            None => panic!("stack is empty"),
        }
    }

    fn set_top(&mut self, val: impl Into<Value>) {
        let len = self.value_stack.len();
        self.value_stack[len - 1] = val.into();
    }

    pub fn load_offset(&self, offset: i16) -> Value {
        self.value_stack[self.stack_base.wrapping_add_signed(offset as isize)]
    }

    pub fn load_offset_or_top(&mut self, arg: u16) -> Value {
        // extract the use_top flag from the high bit
        let use_top = (arg >> 15) as usize;

        // extract the signed offset from the lower 15 bits
        let offset = ((arg << 1) as i16 >> 1) as isize;

        let top_idx = self.value_stack.len().wrapping_sub(1);
        let local_idx = self.stack_base.wrapping_add_signed(offset);

        // if use_top is 1, select the top_idx. if use_top is 0, select the local_idx
        let mask = 0usize.wrapping_sub(use_top);
        let final_index = (top_idx & mask) | (local_idx & !mask);

        let ret = self.value_stack[final_index];
        // if use_top is 1, pop from the stack
        self.value_stack.truncate(self.value_stack.len() - use_top);

        ret
    }

    pub fn store_offset_or_top(&mut self, arg: u16, val: impl Into<Value>) {
        let val = val.into();

        let use_stack = (arg >> 15) as usize;

        let offset = ((arg << 1) as i16 >> 1) as isize;

        let top_idx = self.value_stack.len();
        let local_idx = self.stack_base.wrapping_add_signed(offset);

        let mask = 0usize.wrapping_sub(use_stack);
        let final_index = (top_idx & mask) | (local_idx & !mask);

        // TODO: if both arguments were popped from stack, it would be better to modify top of stack in-place.
        // TODO: pop() pop() push() -> pop()
        // TODO: don't optimize this until later when all instructions use the new dst reg reg strategy. Then make change using bitmasks and profile
        // push value to top if use_stack = 1
        self.value_stack
            .resize(self.value_stack.len() + use_stack, val);
        // assign to stack offset (final_index is stack top if use_stack = 1)
        // this is redundant if use_stack = 1, but better than branching
        self.value_stack[final_index] = val;
    }

    pub fn store_offset(&mut self, offset: i16, v: impl Into<Value>) {
        let index = self.stack_base.wrapping_add_signed(offset as isize);
        if index >= self.value_stack.len() {
            self.fail(VmErrorKind::InternalError(format!(
                "store_offset({}): index={} >= len={}",
                offset,
                index,
                self.value_stack.len()
            )));
        }
        self.value_stack[index] = v.into();
    }

    pub fn pop(&mut self) -> Value {
        match self.value_stack.pop() {
            Some(v) => v,
            None => panic!("underflow"),
        }
    }

    pub fn pop_n(&mut self, n: usize) -> Vec<Value> {
        self.value_stack
            .drain(self.value_stack.len() - n..)
            .collect()
    }

    pub fn push_int(&mut self, n: AbraInt) {
        self.push(n);
    }

    pub fn push_str(&mut self, s: String) {
        let s = StringObject::new(s, self);
        let r = Value::from(s);
        self.push(r);
    }

    pub fn push_bool(&mut self, b: bool) {
        self.push(b);
    }

    pub fn push_float(&mut self, f: AbraFloat) {
        self.push(f);
    }

    pub fn construct_variant(&mut self, tag: u16) {
        let value = self.top();
        let variant = EnumObject::new(tag, value, self);
        let r = Value::from(variant);
        self.set_top(r);
    }

    pub fn construct_tuple(&mut self, n: usize) {
        self.construct_struct(n)
    }

    pub fn construct_struct(&mut self, n: usize) {
        let fields = self.pop_n(n);
        let ptr = StructObject::new(fields, self);
        self.push(ptr);
    }

    pub fn construct_array(&mut self, n: usize) {
        let fields = self.pop_n(n);
        let ptr = ArrayObject::new(fields, self);
        self.push(ptr);
    }

    pub fn deconstruct_struct(&mut self) {
        let val = self.pop();
        let s = val.get_struct(self);
        let fields = s.get_fields();
        self.value_stack.extend(fields.iter().rev());
    }

    pub fn deconstruct_array(&mut self) {
        let val = self.pop();
        let arr = val.get_array(self);
        self.value_stack.extend(arr.data.iter().rev());
    }

    pub fn deconstruct_variant(&mut self) {
        let val = self.top();
        let (val, tag) = {
            let variant = val.get_variant(self);
            (variant.val, variant.tag)
        };
        self.set_top(val);
        self.push(tag as AbraInt);
    }

    pub fn array_len(&mut self) -> usize {
        let val = self.top();
        let arr = val.get_array(self);
        arr.data.len()
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

    fn make_error(&self, kind: VmErrorKind) -> VmError {
        VmError {
            kind,
            location: self.pc_to_error_location(self.pc),
            trace: self.make_stack_trace(),
        }
    }

    fn _fail_wrong_type(&self, expected: ValueKind) -> ! {
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
    StoreOffsetImm(i16, u16),

    // Constants
    PushNil(u16),
    PushBool(bool),
    PushInt(u32),
    PushFloat(u32),
    PushString(u32),
    PushAddr(ProgramCounter),

    // Arithmetic
    AddInt(u16, u16, u16),
    AddIntImm(u16, u16, u16),
    SubtractInt(u16, u16, u16),
    SubIntImm(u16, u16, u16),
    MulInt(u16, u16, u16),
    MulIntImm(u16, u16, u16),
    DivideInt(u16, u16, u16),
    DivideIntImm(u16, u16, u16),
    PowerInt(u16, u16, u16),
    PowerIntImm(u16, u16, u16),
    Modulo(u16, u16, u16),
    ModuloImm(u16, u16, u16),

    AddFloat(u16, u16, u16),
    AddFloatImm(u16, u16, u16),
    SubFloat(u16, u16, u16),
    SubFloatImm(u16, u16, u16),
    MulFloat(u16, u16, u16),
    MulFloatImm(u16, u16, u16),
    DivFloat(u16, u16, u16),
    DivFloatImm(u16, u16, u16),
    PowerFloat(u16, u16, u16),
    PowerFloatImm(u16, u16, u16),

    Ceil(u16, u16),
    Floor(u16, u16),
    Round(u16, u16),
    SquareRoot(u16, u16),
    Sin(u16, u16),
    Cos(u16, u16),
    Tan(u16, u16),
    Asin(u16, u16),
    Acos(u16, u16),
    Atan(u16, u16),
    Log(u16, u16),
    Log2(u16, u16),
    Log10(u16, u16),

    // Logical
    Not(u16, u16),

    // Comparison
    LessThanInt(u16, u16, u16),
    LessThanIntImm(u16, u16, u16),
    LessThanOrEqualInt(u16, u16, u16),
    LessThanOrEqualIntImm(u16, u16, u16),
    GreaterThanInt(u16, u16, u16),
    GreaterThanIntImm(u16, u16, u16),
    GreaterThanOrEqualInt(u16, u16, u16),
    GreaterThanOrEqualIntImm(u16, u16, u16),

    LessThanFloat(u16, u16, u16),
    LessThanFloatImm(u16, u16, u16),
    LessThanOrEqualFloat(u16, u16, u16),
    LessThanOrEqualFloatImm(u16, u16, u16),
    GreaterThanFloat(u16, u16, u16),
    GreaterThanFloatImm(u16, u16, u16),
    GreaterThanOrEqualFloat(u16, u16, u16),
    GreaterThanOrEqualFloatImm(u16, u16, u16),

    EqualInt(u16, u16, u16),
    EqualIntImm(u16, u16, u16),
    EqualFloat(u16, u16, u16),
    EqualFloatImm(u16, u16, u16),
    EqualBool(u16, u16, u16),
    EqualString(u16, u16, u16),

    // Control Flow
    Jump(ProgramCounter),
    JumpIf(ProgramCounter),
    JumpIfFalse(ProgramCounter),
    // JumpIfLessThan(ProgramCounter), // TODO: when jumps are relative and only i16, can add this back
    Call(CallData),
    CallFuncObj(u32),
    CallExtern(u32),
    Return(u32),
    ReturnVoid,
    Stop, // used when returning from main function
    HostFunc(u16),
    Panic,

    // Data Structures
    ConstructStruct(u16),
    ConstructArray(u16),
    // TODO: it's a shame that simple enums like Red | Blue | Green aren't just represented as an int.
    // TODO: there should be two types of enums: primitive and object enums. Primitive enums are basically just ints and don't require allocations
    // TODO: pattern matching with primitive enums should also be much much faster, equivalent to a switch.
    // TODO: and equality comparison should be as cheap as int comparison
    ConstructVariant { tag: u16 },
    DeconstructStruct,
    DeconstructArray,
    DeconstructVariant,

    GetField(u16, u16),
    SetField(u16, u16),
    GetIndex(u16, u16),
    SetIndex(u16, u16),

    MakeClosure(u16),

    ArrayPush(u16, u16),
    ArrayPushIntImm(u16, u16),
    ArrayLength(u16, u16),
    ArrayPop(u16, u16),
    ConcatStrings(u16, u16, u16),
    IntToFloat(u16, u16),
    FloatToInt(u16, u16),
    IntToString(u16, u16),
    FloatToString(u16, u16),

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

// TODO: this wouldn't be necessary if jumps used i16 offsets
impl CallData {
    const NARGS_NBITS: u32 = 5;
    const NARGS_SHIFT: u32 = 32 - Self::NARGS_NBITS;
    const NARGS_MASK: u32 = 0b11111 << Self::NARGS_SHIFT;
    const ADDR_MASK: u32 = !Self::NARGS_MASK;

    pub(crate) fn new(nargs: u32, addr: u32) -> Self {
        debug_assert!(addr <= Self::ADDR_MASK);
        let repr = addr | nargs << Self::NARGS_SHIFT;
        CallData(repr)
    }

    fn get_addr(&self) -> u32 {
        self.0 & Self::ADDR_MASK
    }

    fn get_nargs(&self) -> u32 {
        self.0 >> Self::NARGS_SHIFT
    }
}

// Value is 16 bytes
// While this wastes memory, the extra space could be used down the line for
// - builtin Vec3(f32,f32,f32) type
// - small-string optimization (inline string inside Value). Especially useful for single char strings
// - vtable index
const _: [(); 16] = [(); size_of::<Value>()];
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Value(u64, /*is_pointer*/ bool);

impl Value {
    pub fn get_int(&self, _vm: &Vm) -> AbraInt {
        self.0 as AbraInt
    }

    pub fn get_float(&self, _vm: &Vm) -> AbraFloat {
        AbraFloat::from_bits(self.0)
    }

    pub fn get_bool(&self, _vm: &Vm) -> bool {
        self.0 != 0
    }

    unsafe fn get_object_header<'a>(&self) -> &'a mut ObjectHeader {
        unsafe { &mut *(self.0 as *mut ObjectHeader) }
    }

    fn get_struct<'a>(&self, _vm: &mut Vm) -> &'a StructObject {
        unsafe { &*(self.0 as *const StructObject) }
    }

    unsafe fn get_struct_mut<'a>(&self, _vm: &mut Vm) -> &'a mut StructObject {
        unsafe { &mut *(self.0 as *mut StructObject) }
    }

    fn get_array<'a>(&self, _vm: &mut Vm) -> &'a ArrayObject
    where
        Self: Sized,
    {
        unsafe { &*(self.0 as *const ArrayObject) }
    }

    unsafe fn get_array_mut<'a>(&self, _vm: &mut Vm) -> &'a mut ArrayObject
    where
        Self: Sized,
    {
        unsafe { &mut *(self.0 as *mut ArrayObject) }
    }

    fn get_variant<'a>(&self, _vm: &Vm) -> &'a EnumObject
    where
        Self: Sized,
    {
        unsafe { &mut *(self.0 as *mut EnumObject) }
    }

    pub fn view_string<'a>(&self, _vm: &Vm) -> &'a str {
        let so = unsafe { &*(self.0 as *const StringObject) };
        &so.str
    }

    fn get_addr(&self, _vm: &Vm) -> ProgramCounter {
        ProgramCounter(self.0 as u32)
    }
}

impl From<bool> for Value {
    fn from(b: bool) -> Self {
        Self(if b { 1 } else { 0 }, false)
    }
}

impl From<AbraInt> for Value {
    fn from(n: AbraInt) -> Self {
        Self(n as u64, false)
    }
}

impl From<AbraFloat> for Value {
    fn from(n: AbraFloat) -> Self {
        Self(AbraFloat::to_bits(n), false)
    }
}

impl From<ProgramCounter> for Value {
    fn from(n: ProgramCounter) -> Self {
        Self(n.0 as u64, false)
    }
}

impl From<*mut ArrayObject> for Value {
    fn from(ptr: *mut ArrayObject) -> Self {
        Self(ptr as u64, true)
    }
}

impl From<*mut StructObject> for Value {
    fn from(ptr: *mut StructObject) -> Self {
        Self(ptr as u64, true)
    }
}

impl From<*mut EnumObject> for Value {
    fn from(ptr: *mut EnumObject) -> Self {
        Self(ptr as u64, true)
    }
}

impl From<*mut StringObject> for Value {
    fn from(ptr: *mut StringObject) -> Self {
        Self(ptr as u64, true)
    }
}

#[derive(Debug)]
struct CallFrame {
    pc: ProgramCounter,
    stack_base: usize,
    nargs: u32,
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
    visited: bool,
}

impl ObjectHeader {
    unsafe fn dealloc(&mut self, heap_size: &mut usize) {
        let kind = self.kind;
        match kind {
            ObjectKind::String => {
                let ptr = self as *mut Self as *mut StringObject;
                let obj = unsafe { &mut *ptr };
                *heap_size -= obj.nbytes();
                let _ = unsafe { Box::from_raw(ptr) };
            }
            ObjectKind::Enum => {
                let ptr = self as *mut Self as *mut EnumObject;
                let obj = unsafe { &mut *ptr };
                *heap_size -= obj.nbytes();
                let _ = unsafe { Box::from_raw(ptr) };
            }
            ObjectKind::Struct => {
                let obj = unsafe { &*(self as *mut Self as *mut StructObject) };
                let layout = obj.layout();
                *heap_size -= obj.nbytes();
                unsafe { dealloc(self as *mut ObjectHeader as *mut u8, layout) };
            }
            ObjectKind::Array => {
                let ptr = self as *mut Self as *mut ArrayObject;
                let obj = unsafe { &mut *ptr };
                *heap_size -= obj.nbytes();
                let _ = unsafe { Box::from_raw(ptr) };
            }
        }
    }

    fn nbytes(&self) -> usize {
        let kind = self.kind;
        match kind {
            ObjectKind::String => {
                let ptr = self as *const Self as *const StringObject;
                let obj = unsafe { &*ptr };
                obj.nbytes()
            }
            ObjectKind::Enum => {
                let ptr = self as *const Self as *const EnumObject;
                let obj = unsafe { &*ptr };
                obj.nbytes()
            }
            ObjectKind::Struct => {
                let obj = unsafe { &*(self as *const Self as *const StructObject) };
                obj.nbytes()
            }
            ObjectKind::Array => {
                let ptr = self as *const Self as *const ArrayObject;
                let obj = unsafe { &*ptr };
                obj.nbytes()
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
                        visited: match &vm.gc_state {
                            GcState::Idle => false,
                            GcState::Marking | GcState::Sweeping { .. } => true,
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

            vm.heap_list.push(obj as *mut ObjectHeader);
            if vm.gc_state == GcState::Marking {
                vm.gray_stack.push(obj as *mut ObjectHeader);
            }
            vm.heap_size += layout.size();
            vm.gc_debt += layout.size();

            obj
        }
    }

    fn header_ptr(self: &mut StructObject) -> *mut ObjectHeader {
        self as *mut Self as *mut ObjectHeader
    }

    fn layout(&self) -> Layout {
        Self::layout_helper(self.len)
    }

    fn nbytes(&self) -> usize {
        self.layout().size()
    }

    fn layout_helper(len: usize) -> Layout {
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
    data: Vec<Value>,
}

impl ArrayObject {
    fn new(data: Vec<Value>, vm: &mut Vm) -> *mut ArrayObject {
        let header = ObjectHeader {
            kind: ObjectKind::Array,
            visited: match &vm.gc_state {
                GcState::Idle => false,
                GcState::Marking | GcState::Sweeping { .. } => true,
            },
        };
        let b = Box::new(ArrayObject { header, data });
        let arr = Box::leak(b);

        vm.heap_list
            .push(arr as *mut ArrayObject as *mut ObjectHeader);
        if vm.gc_state == GcState::Marking {
            vm.gray_stack
                .push(arr as *mut ArrayObject as *mut ObjectHeader);
        }
        vm.heap_size += arr.nbytes();
        vm.gc_debt += arr.nbytes();

        arr
    }

    fn header_ptr(&mut self) -> *mut ObjectHeader {
        self as *mut Self as *mut ObjectHeader
    }

    fn nbytes(&self) -> usize {
        size_of::<Self>() + self.data.capacity() * size_of::<Value>()
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
            visited: match &vm.gc_state {
                GcState::Idle => false,
                GcState::Marking | GcState::Sweeping { .. } => true,
            },
        };
        let b = Box::new(EnumObject { header, tag, val });
        let variant = Box::leak(b);

        vm.heap_list
            .push(variant as *mut EnumObject as *mut ObjectHeader);
        if vm.gc_state == GcState::Marking {
            vm.gray_stack
                .push(variant as *mut EnumObject as *mut ObjectHeader);
        }
        vm.heap_size += variant.nbytes();
        vm.gc_debt += variant.nbytes();

        variant
    }

    fn nbytes(&self) -> usize {
        size_of::<Self>()
    }
}

#[repr(C)]
struct StringObject {
    header: ObjectHeader,
    str: String,
}

impl StringObject {
    fn new(str: String, vm: &mut Vm) -> *mut StringObject {
        let header = ObjectHeader {
            kind: ObjectKind::String,
            visited: match &vm.gc_state {
                GcState::Idle => false,
                GcState::Marking | GcState::Sweeping { .. } => true,
            },
        };
        let b = Box::new(StringObject { header, str });
        let str = Box::leak(b);

        vm.heap_list
            .push(str as *mut StringObject as *mut ObjectHeader);
        if vm.gc_state == GcState::Marking {
            vm.gray_stack
                .push(str as *mut StringObject as *mut ObjectHeader);
        }
        vm.heap_size += str.nbytes();
        vm.gc_debt += str.nbytes();

        str
    }

    fn nbytes(&self) -> usize {
        size_of::<StringObject>() + self.str.capacity()
    }
}

impl Vm {
    pub fn run(&mut self) {
        self.validate();
        loop {
            if !self.step() {
                return;
            }
            self.maybe_gc();
        }
    }

    pub fn run_n_steps(&mut self, mut steps: u32) {
        self.validate();
        while steps > 0 {
            self.maybe_gc();
            if !self.step() {
                return;
            }

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
                    self.push(0);
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
                let s = self.static_strings[idx as usize];
                self.push(s);
            }
            Instr::PushAddr(addr) => {
                self.push(addr);
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
            Instr::StoreOffsetImm(n, imm) => {
                self.store_offset(n, self.int_constants[imm as usize]);
            }
            Instr::AddInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_add(b) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::AddIntImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_add(self.int_constants[imm as usize]) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::SubtractInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_sub(b) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::SubIntImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_sub(self.int_constants[imm as usize]) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::MulInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_mul(b) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::MulIntImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_mul(self.int_constants[imm as usize]) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::DivideInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                if b == 0 {
                    self.error = Some(self.make_error(VmErrorKind::DivisionByZero).into());
                    return false;
                }
                let Some(c) = a.checked_div(b) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::DivideIntImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_div(self.int_constants[imm as usize]) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::PowerInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_pow(b as u32) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::PowerIntImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_int(self);
                let Some(c) = a.checked_pow(self.int_constants[imm as usize] as u32) else {
                    self.error = Some(
                        self.make_error(VmErrorKind::IntegerOverflowUnderflow)
                            .into(),
                    );
                    return false;
                };
                self.store_offset_or_top(dest, c);
            }
            Instr::Modulo(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a.rem_euclid(b));
            }
            Instr::ModuloImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a.rem_euclid(self.int_constants[imm as usize]));
            }
            Instr::AddFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a + b);
            }
            Instr::AddFloatImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a + self.float_constants[imm as usize]);
            }
            Instr::SubFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a - b);
            }
            Instr::SubFloatImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a - self.float_constants[imm as usize]);
            }
            Instr::MulFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a * b);
            }
            Instr::MulFloatImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a * self.float_constants[imm as usize]);
            }
            Instr::DivFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                if b == 0.0 {
                    self.error = Some(self.make_error(VmErrorKind::DivisionByZero).into());
                    return false;
                }
                self.store_offset_or_top(dest, a / b);
            }
            Instr::DivFloatImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a / self.float_constants[imm as usize]);
            }
            Instr::PowerFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.powf(b));
            }
            Instr::PowerFloatImm(dest, reg1, imm) => {
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.powf(self.float_constants[imm as usize]));
            }
            Instr::Ceil(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.ceil());
            }
            Instr::Floor(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.floor());
            }
            Instr::Round(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.round());
            }
            Instr::SquareRoot(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.sqrt());
            }
            Instr::Sin(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.sin());
            }
            Instr::Cos(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.cos());
            }
            Instr::Tan(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.tan());
            }
            Instr::Asin(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.asin());
            }
            Instr::Acos(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.acos());
            }
            Instr::Atan(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.atan());
            }
            Instr::Log(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.ln());
            }
            Instr::Log2(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.log2());
            }
            Instr::Log10(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_float(self);
                self.store_offset_or_top(dest, a.log10());
            }
            Instr::Not(dest, reg) => {
                let a = self.load_offset_or_top(reg).get_bool(self);
                self.store_offset_or_top(dest, !a);
            }
            Instr::LessThanInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a < b);
            }
            Instr::LessThanIntImm(dest, reg1, imm) => {
                let b = self.int_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a < b);
            }
            Instr::LessThanOrEqualInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a <= b);
            }
            Instr::LessThanOrEqualIntImm(dest, reg1, imm) => {
                let b = self.int_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a <= b);
            }
            Instr::GreaterThanInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a > b);
            }
            Instr::GreaterThanIntImm(dest, reg1, imm) => {
                let b = self.int_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a > b);
            }
            Instr::GreaterThanOrEqualInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a >= b);
            }
            Instr::GreaterThanOrEqualIntImm(dest, reg1, imm) => {
                let b = self.int_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a >= b);
            }
            Instr::LessThanFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_lt());
            }
            Instr::LessThanFloatImm(dest, reg1, imm) => {
                let b = self.float_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_lt());
            }
            Instr::LessThanOrEqualFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_le());
            }
            Instr::LessThanOrEqualFloatImm(dest, reg1, imm) => {
                let b = self.float_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_le());
            }
            Instr::GreaterThanFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_gt());
            }
            Instr::GreaterThanFloatImm(dest, reg1, imm) => {
                let b = self.float_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_gt());
            }
            Instr::GreaterThanOrEqualFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_ge());
            }
            Instr::GreaterThanOrEqualFloatImm(dest, reg1, imm) => {
                let b = self.float_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_ge());
            }
            Instr::EqualInt(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_int(self);
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a == b);
            }
            Instr::EqualIntImm(dest, reg1, imm) => {
                let b = self.int_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_int(self);
                self.store_offset_or_top(dest, a == b);
            }
            Instr::EqualFloat(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_float(self);
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_eq());
            }
            Instr::EqualFloatImm(dest, reg1, imm) => {
                let b = self.float_constants[imm as usize];
                let a = self.load_offset_or_top(reg1).get_float(self);
                self.store_offset_or_top(dest, a.total_cmp(&b).is_eq());
            }
            Instr::EqualBool(dest, reg1, reg2) => {
                let b = self.load_offset_or_top(reg2).get_bool(self);
                let a = self.load_offset_or_top(reg1).get_bool(self);
                self.store_offset_or_top(dest, a == b);
            }
            Instr::EqualString(dest, reg1, reg2) => {
                if self.string_op_index1 == 0 {
                    self.string_operand2 = self.load_offset_or_top(reg2);
                    self.string_operand1 = self.load_offset_or_top(reg1);
                }
                let b = self.string_operand2.view_string(self);
                let a = self.string_operand1.view_string(self);
                // if we've already looked at every character, true
                if self.string_op_index1 == a.len() && self.string_op_index1 == b.len() {
                    self.store_offset_or_top(dest, true);
                    self.string_op_index1 = 0;
                }
                // if the strings are different lengths or the ith character is different, false
                else if a.len() != b.len()
                    || a.as_bytes()[self.string_op_index1] != b.as_bytes()[self.string_op_index1]
                {
                    self.store_offset_or_top(dest, false);
                    self.string_op_index1 = 0;
                } else {
                    self.pc.0 -= 1;
                    self.string_op_index1 += 1;
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
                    nargs,
                });
                self.pc = ProgramCounter(target);
                self.stack_base = self.value_stack.len();
            }
            Instr::CallFuncObj(nargs) => {
                let top = self.pop();
                let mut fields = top.get_struct(self).get_fields().iter();
                let addr = fields.next().unwrap().get_addr(self);
                self.call_stack.push(CallFrame {
                    pc: self.pc,
                    stack_base: self.stack_base,
                    nargs,
                });

                self.pc = addr;
                self.stack_base = self.value_stack.len();

                // captured values
                self.value_stack.extend(fields);
            }
            Instr::Return(nargs) => {
                let idx = self.stack_base - nargs as usize;
                let v = self.top();
                self.value_stack[idx] = v;

                let frame = self.call_stack.pop().unwrap();
                self.pc = frame.pc;
                self.value_stack
                    .truncate(self.stack_base - (frame.nargs as usize) + 1);
                self.stack_base = frame.stack_base;
            }
            Instr::ReturnVoid => {
                let frame = self.call_stack.pop().unwrap();
                self.pc = frame.pc;
                self.value_stack
                    .truncate(self.stack_base - (frame.nargs as usize));
                self.stack_base = frame.stack_base;
            }
            Instr::Stop => {
                self.done = true;
                return false;
            }
            Instr::Panic => {
                let msg = self.pop().view_string(self);
                self.error = Some(Box::new(
                    self.make_error(VmErrorKind::Panic(msg.to_string())),
                ));
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
            Instr::GetField(index, offset) => {
                let val = self.load_offset_or_top(offset);
                let s = val.get_struct(self);
                let field = s.get_fields()[index as usize];
                self.push(field);
            }
            Instr::SetField(index, offset) => {
                let val = self.load_offset_or_top(offset);
                let rvalue = self.pop();
                let s = unsafe { val.get_struct_mut(self) };

                self.write_barrier(s.header_ptr(), rvalue);
                s.get_fields_mut()[index as usize] = rvalue;
            }
            Instr::GetIndex(reg1, reg2) => {
                let val = self.load_offset_or_top(reg2);
                let idx = self.load_offset_or_top(reg1).get_int(self);
                let arr = val.get_array(self);
                if idx as usize >= arr.data.len() || idx < 0 {
                    self.error = Some(self.make_error(VmErrorKind::ArrayOutOfBounds).into());
                    return false;
                }
                let field = arr.data[idx as usize];
                self.push(field);
            }
            Instr::SetIndex(reg1, reg2) => {
                let val = self.load_offset_or_top(reg2);
                let idx = self.load_offset_or_top(reg1).get_int(self);
                let rvalue = self.pop();
                let arr = unsafe { val.get_array_mut(self) };
                if idx as usize >= arr.data.len() || idx < 0 {
                    self.error = Some(self.make_error(VmErrorKind::ArrayOutOfBounds).into());
                    return false;
                }
                self.write_barrier(arr.header_ptr(), rvalue);
                arr.data[idx as usize] = rvalue;
            }
            Instr::ConstructVariant { tag } => {
                self.construct_variant(tag);
            }
            Instr::MakeClosure(ncaptures) => {
                self.construct_struct(ncaptures as usize + 1);
            }
            Instr::ArrayPush(reg1, reg2) => {
                let rvalue = self.load_offset_or_top(reg2);
                let val = self.load_offset_or_top(reg1);
                let arr = unsafe { val.get_array_mut(self) };

                let cap1 = arr.data.capacity();
                self.write_barrier(arr.header_ptr(), rvalue);
                arr.data.push(rvalue);
                let cap2 = arr.data.capacity();
                self.heap_size += (cap2 - cap1) * size_of::<Value>();
                self.gc_debt += (cap2 - cap1) * size_of::<Value>();
            }
            Instr::ArrayPushIntImm(reg1, imm) => {
                let rvalue = self.int_constants[imm as usize];
                let val = self.load_offset_or_top(reg1);
                let arr = unsafe { val.get_array_mut(self) };

                let cap1 = arr.data.capacity();
                arr.data.push(Value::from(rvalue));
                let cap2 = arr.data.capacity();
                self.heap_size += (cap2 - cap1) * size_of::<Value>();
                self.gc_debt += (cap2 - cap1) * size_of::<Value>();
            }
            Instr::ArrayLength(dest, reg) => {
                let val = self.load_offset_or_top(reg);
                let arr = val.get_array(self);
                self.store_offset_or_top(dest, arr.data.len() as AbraInt);
            }
            Instr::ArrayPop(dest, reg) => {
                let val = self.load_offset_or_top(reg);
                let arr = unsafe { val.get_array_mut(self) };
                let lvalue = arr.data.pop().unwrap();
                self.store_offset_or_top(dest, lvalue);
            }
            Instr::ConcatStrings(dest, reg1, reg2) => {
                if self.string_op_index1 == 0 && self.string_op_index2 == 0 {
                    self.string_operand2 = self.load_offset_or_top(reg2);
                    self.string_operand1 = self.load_offset_or_top(reg1);
                    let b = self.string_operand2.view_string(self);
                    let a = self.string_operand1.view_string(self);
                    self.concat_string_builder = Vec::with_capacity(a.len() + b.len());
                }
                let b = self.string_operand2.view_string(self);
                let a = self.string_operand1.view_string(self);
                // if we've already looked at every character, true
                if self.string_op_index1 == a.len() && self.string_op_index2 == b.len() {
                    let mut builder = vec![];
                    std::mem::swap(&mut builder, &mut self.concat_string_builder);
                    let s = String::from_utf8(builder).unwrap();
                    let s = StringObject::new(s, self);
                    self.store_offset_or_top(dest, s);
                    self.string_op_index1 = 0;
                    self.string_op_index2 = 0;
                }
                // if there's a character left in string 1, write a character from it
                else if self.string_op_index1 < a.len() {
                    self.concat_string_builder
                        .push(a.as_bytes()[self.string_op_index1]);
                    self.string_op_index1 += 1;
                    self.pc.0 -= 1;
                }
                // if there's a character left in string 2, write a character from it
                else if self.string_op_index2 < b.len() {
                    self.concat_string_builder
                        .push(b.as_bytes()[self.string_op_index2]);
                    self.string_op_index2 += 1;
                    self.pc.0 -= 1;
                }
            }
            Instr::IntToFloat(dest, reg) => {
                let n = self.load_offset_or_top(reg).get_int(self);
                let f = n as f64;
                self.store_offset_or_top(dest, f);
            }
            Instr::FloatToInt(dest, reg) => {
                let f = self.load_offset_or_top(reg).get_float(self);
                let n = f as AbraInt;
                self.store_offset_or_top(dest, n);
            }
            Instr::IntToString(dest, reg) => {
                let n = self.load_offset_or_top(reg).get_int(self);
                let s = n.to_string();
                let s = StringObject::new(s, self);
                self.store_offset_or_top(dest, s);
            }
            Instr::FloatToString(dest, reg) => {
                let f = self.load_offset_or_top(reg).get_float(self);
                let s = f.to_string();
                let s = StringObject::new(s, self);
                self.store_offset_or_top(dest, s);
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
                        self.fail(VmErrorKind::LibLoadFailure(libname.to_string()))
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
                        self.fail(VmErrorKind::SymbolLoadFailure(symbol_name.to_string()));
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

    fn make_stack_trace(&self) -> Vec<VmErrorLocation> {
        let mut ret = vec![];
        for frame in &self.call_stack {
            ret.push(self.pc_to_error_location(frame.pc));
        }
        ret
    }

    // GARBAGE COLLECTION

    pub fn maybe_gc(&mut self) {
        match self.gc_state {
            GcState::Idle => {
                let threshold = self.last_gc_heap_size * GC_PAUSE_FACTOR;
                if self.heap_size > threshold {
                    self.start_mark_phase();
                }
            }
            GcState::Marking => {
                // process a few gray nodes
                let mut slice = GC_STEP_FACTOR * self.gc_debt;
                self.process_gray(&mut slice);
            }
            GcState::Sweeping { .. } => {
                let slice = GC_STEP_FACTOR * self.gc_debt;
                self.sweep(slice);
            }
        }
    }

    fn start_mark_phase(&mut self) {
        // mark roots gray
        for v in self.value_stack.iter() {
            Self::mark(v, &mut self.gray_stack, self.gc_visited);
        }
        for s_ptr in self.static_strings.iter().cloned() {
            Self::mark(&Value::from(s_ptr), &mut self.gray_stack, self.gc_visited);
        }
        Self::mark(&self.string_operand1, &mut self.gray_stack, self.gc_visited);
        Self::mark(&self.string_operand2, &mut self.gray_stack, self.gc_visited);

        self.gc_state = GcState::Marking;
    }

    fn mark(v: &Value, gray_stack: &mut Vec<*mut ObjectHeader>, gc_visited: bool) {
        // if v is not a pointer
        if !v.1 {
            return;
        }

        let header = unsafe { v.get_object_header() };
        if header.visited == gc_visited {
            return;
        }

        header.visited = gc_visited;
        gray_stack.push(header)
    }

    fn process_gray(&mut self, batch: &mut usize) {
        while *batch > 0
            && let Some(header_ptr) = self.gray_stack.pop()
        {
            {
                let header = unsafe { &mut *header_ptr };
                header.visited = self.gc_visited;
            }

            let kind = {
                let header = unsafe { &mut *header_ptr };
                header.kind
            };

            match kind {
                ObjectKind::String => {
                    let obj = unsafe { &*(header_ptr as *const StringObject) };
                    *batch -= obj.nbytes();
                }
                ObjectKind::Enum => {
                    let obj = unsafe { &*(header_ptr as *const EnumObject) };
                    *batch -= obj.nbytes();
                    Self::mark(&obj.val, &mut self.gray_stack, self.gc_visited);
                }
                ObjectKind::Struct => {
                    let obj = unsafe { &*(header_ptr as *const StructObject) };
                    *batch -= obj.nbytes();
                    for field in obj.get_fields() {
                        Self::mark(field, &mut self.gray_stack, self.gc_visited);
                    }
                }
                ObjectKind::Array => {
                    let obj = unsafe { &*(header_ptr as *const ArrayObject) };
                    *batch -= obj.nbytes();
                    for elem in &obj.data {
                        Self::mark(elem, &mut self.gray_stack, self.gc_visited);
                    }
                }
            }
        }
        if self.gray_stack.is_empty() {
            self.gc_state = GcState::Sweeping { index: 0 };
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
        if parent.visited == self.gc_visited {
            let header = unsafe { child.get_object_header() };
            if header.visited != self.gc_visited {
                header.visited = self.gc_visited;
                self.gray_stack.push(header);
            }
        }
    }

    fn sweep(&mut self, batch: usize) {
        if let GcState::Sweeping { index } = &mut self.gc_state {
            let mut work_done = 0;

            while work_done < batch && *index < self.heap_list.len() {
                let header_ptr = self.heap_list[*index];
                let header = unsafe { &mut *header_ptr };
                work_done += header.nbytes();

                if header.visited != self.gc_visited {
                    unsafe { header.dealloc(&mut self.heap_size) };

                    self.heap_list.swap_remove(*index);
                } else {
                    // object is alive. reset to white for next cycle
                    header.visited = !self.gc_visited;
                    *index += 1;
                }
            }

            if *index >= self.heap_list.len() {
                self.gc_state = GcState::Idle;
                self.last_gc_heap_size = self.heap_size;
            }
        }
    }

    pub fn compact(&mut self) {
        self.value_stack.shrink_to_fit();
        self.call_stack.shrink_to_fit();
    }

    pub fn nbytes(&self) -> usize {
        // TODO: should anything else be taken into account?
        self.program.len() * size_of::<Instr>()
            + self.value_stack.len() * size_of::<Value>()
            + self.call_stack.len() * size_of::<CallFrame>()
            + self.heap_size
    }
}

impl Drop for Vm {
    fn drop(&mut self) {
        for header_ptr in &self.heap_list {
            let header = unsafe { &mut **header_ptr };
            unsafe { header.dealloc(&mut self.heap_size) };
        }
    }
}

impl Vm {
    fn push(&mut self, x: impl Into<Value>) {
        self.value_stack.push(x.into());
    }

    pub fn pop_int(&mut self) -> AbraInt {
        self.pop().get_int(self)
    }

    pub fn pop_float(&mut self) -> AbraFloat {
        self.pop().get_float(self)
    }

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
