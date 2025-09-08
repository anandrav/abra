// This is an auto-generated file.
use abra_core::addons::*;
use abra_core::vm::*;
use std::ffi::c_void;
pub enum HostFunction {
    PrintString,
    Foo,
    Bar,
}
pub enum HostFunctionArgs {
    PrintString(String),
    Foo(i64),
    Bar(i64, i64),
}
impl HostFunctionArgs {
    pub(crate) fn from_vm(vm: &mut Vm, pending_effect: u16) -> Self {
        let vm_funcs = &AbraVmFunctions::new();
        match pending_effect {
            0 => {
                let arg0: String =
                    unsafe { <String>::from_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
                HostFunctionArgs::PrintString(arg0)
            }
            1 => {
                let arg0: i64 = unsafe { <i64>::from_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
                HostFunctionArgs::Foo(arg0)
            }
            2 => {
                let arg0: i64 = unsafe { <i64>::from_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
                let arg1: i64 = unsafe { <i64>::from_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
                HostFunctionArgs::Bar(arg0, arg1)
            }
            _ => panic!("unexpected tag encountered: {pending_effect}"),
        }
    }
}
pub enum HostFunctionRet {
    PrintString,
    Foo(i64),
    Bar(i64),
}
impl HostFunctionRet {
    pub(crate) fn to_vm(self, vm: &mut Vm) {
        let vm_funcs = &AbraVmFunctions::new();
        match self {
            HostFunctionRet::PrintString => {
                unsafe { ().to_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
            }
            HostFunctionRet::Foo(i64) => {
                unsafe { (i64).to_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
            }
            HostFunctionRet::Bar(i64) => {
                unsafe { (i64).to_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
            }
        }
    }
}
impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
            0 => HostFunction::PrintString,
            1 => HostFunction::Foo,
            2 => HostFunction::Bar,
            i => panic!("unrecognized host func: {i}"),
        }
    }
}
