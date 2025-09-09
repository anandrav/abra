// This is an auto-generated file.

use abra_core::addons::*;
use abra_core::vm::*;
use std::ffi::c_void;
pub enum HostFunctionArgs {
    PrintString(String),
    Readline,
    Foo(i64),
    Bar(i64, i64),
}
impl HostFunctionArgs {
    pub(crate) fn from_vm(vm: &mut Vm, pending_host_func: u16) -> Self {
        match pending_host_func {
            0 => {
                let arg0: String =
                    unsafe { <String>::from_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
                HostFunctionArgs::PrintString(arg0)
            }
            1 => HostFunctionArgs::Readline,
            2 => {
                let arg0: i64 =
                    unsafe { <i64>::from_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
                HostFunctionArgs::Foo(arg0)
            }
            3 => {
                let arg0: i64 =
                    unsafe { <i64>::from_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
                let arg1: i64 =
                    unsafe { <i64>::from_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
                HostFunctionArgs::Bar(arg0, arg1)
            }
            _ => panic!("unexpected tag encountered: {pending_host_func}"),
        }
    }
}
pub enum HostFunctionRet {
    PrintString,
    Readline(String),
    Foo(i64),
    Bar(i64, i64),
}
impl HostFunctionRet {
    pub(crate) fn into_vm(self, vm: &mut Vm) {
        match self {
            HostFunctionRet::PrintString => {
                unsafe { ().to_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
            }
            HostFunctionRet::Readline(out) => {
                unsafe { out.to_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
            }
            HostFunctionRet::Foo(out) => {
                unsafe { out.to_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
            }
            HostFunctionRet::Bar(out0, out1) => {
                unsafe { (out0, out1).to_vm(vm as *mut Vm as *mut c_void, &ABRA_VM_FUNCS) };
            }
        }
    }
}
