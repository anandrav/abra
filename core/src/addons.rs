// Rust addon API

use core::str;
use std::ffi::{c_char, CString};

use crate::vm::Vm;

#[no_mangle]
pub unsafe extern "C" fn vm_push_int(vm: *mut Vm, n: i64) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.push_int(n);
}

#[no_mangle]
pub unsafe extern "C" fn vm_pop_int(vm: *mut Vm) -> i64 {
    let vm = unsafe { vm.as_mut().unwrap() };
    let top = vm.top().get_int();
    vm.pop();
    top
}

#[no_mangle]
pub unsafe extern "C" fn vm_pop(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.pop();
}

#[repr(C)]
pub struct StringView {
    pub ptr: *const c_char,
    pub len: usize,
}

impl StringView {
    pub fn to_owned(self) -> String {
        unsafe {
            let byte_slice = std::slice::from_raw_parts(self.ptr as *const u8, self.len);
            str::from_utf8(byte_slice).unwrap().to_string()
        }
    }

    pub fn from_string(s: &String) -> Self {
        StringView {
            ptr: s.as_ptr() as *const c_char,
            len: s.len(),
        }
    }
}

#[no_mangle]
pub unsafe extern "C" fn vm_view_string(vm: *mut Vm) -> StringView {
    let vm = unsafe { vm.as_mut().unwrap() };
    let top = vm.top().view_string(&vm);
    StringView {
        ptr: top.as_ptr() as *const c_char,
        len: top.len(),
    }
}

#[no_mangle]
pub unsafe extern "C" fn vm_push_string(vm: *mut Vm, string_view: StringView) {
    let vm = unsafe { vm.as_mut().unwrap() };
    let s = string_view.to_owned();
    vm.push_str(&s);
}
