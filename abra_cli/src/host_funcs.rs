// This is an auto-generated file.
use abra_core::addons::*;
use abra_core::vm::*;
use std::ffi::c_void;
pub enum HostFunction {
    PrintString,
}
pub enum HostFunctionArgs {
    PrintString(String),
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
            _ => panic!("unexpected tag encountered: {pending_effect}"),
        }
    }
}
pub enum HostFunctionRet {
    PrintString,
}
impl HostFunctionRet {
    pub(crate) fn to_vm(self, vm: &mut Vm) {
        let vm_funcs = &AbraVmFunctions::new();
        match self {
            HostFunctionRet::PrintString => {
                unsafe { ().to_vm(vm as *mut Vm as *mut c_void, vm_funcs) };
            }
        }
    }
}
impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
            0 => HostFunction::PrintString,
            i => panic!("unrecognized host func: {i}"),
        }
    }
}
