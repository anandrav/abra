// This is an auto-generated file.

use abra_core::addons::*;
use abra_core::vm::*;
use std::ffi::c_void;
pub enum HostFunctionArgs {
    PrintString(String),
    Readline,
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
            1 => HostFunctionArgs::Readline,
            _ => panic!("unexpected tag encountered: {pending_effect}"),
        }
    }
}
pub enum HostFunctionRet {
    PrintString,
    Readline(String),
}
impl HostFunctionRet {
    pub(crate) fn into_vm(self, vm: &mut Vm) {
        let vm_funcs = &AbraVmFunctions::new();
        match self {
            HostFunctionRet::PrintString => {
                unsafe { ().to_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
            }
            HostFunctionRet::Readline(elem0) => {
                unsafe { (elem0).to_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
            }
        }
    }
}
