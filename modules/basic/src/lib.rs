use std::ffi::{c_char, CString};

use abra_core::{addons::*, vm::Vm};

#[no_mangle]
pub unsafe extern "C" fn add(vm: *mut Vm) {
    let n1 = unsafe { vm_pop_int(vm) };
    let n2 = unsafe { vm_pop_int(vm) };
    let ret = n1 + n2;
    unsafe { vm_push_int(vm, ret) };
}
