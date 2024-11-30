// Rust addon API

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
