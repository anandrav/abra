// This is an auto-generated file.

use abra_core::host::*;
use abra_core::vm::*;

#[allow(dead_code)]
pub enum HostFunction {
    Bar,
    Foo,
    PrintString,
    Readline,
}
impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
            0 => HostFunction::Bar,
            1 => HostFunction::Foo,
            2 => HostFunction::PrintString,
            3 => HostFunction::Readline,
            i => panic!("unrecognized host func: {i}"),
        }
    }
}
pub enum HostFunctionArgs {
    Bar(i64, i64),
    Foo(i64, String),
    PrintString(String),
    Readline,
}
impl HostFunctionArgs {
    pub(crate) fn from_vm(vm: &mut Vm, pending_host_func: u16) -> Self {
        match pending_host_func {
            0 => {
                let arg1: i64 = <i64>::from_vm(vm);
                let arg0: i64 = <i64>::from_vm(vm);
                HostFunctionArgs::Bar(arg0, arg1)
            }
            1 => {
                let arg1: String = <String>::from_vm(vm);
                let arg0: i64 = <i64>::from_vm(vm);
                HostFunctionArgs::Foo(arg0, arg1)
            }
            2 => {
                let arg0: String = <String>::from_vm(vm);
                HostFunctionArgs::PrintString(arg0)
            }
            3 => HostFunctionArgs::Readline,
            _ => panic!("unexpected tag encountered: {pending_host_func}"),
        }
    }
}
pub enum HostFunctionRet {
    Bar(i64, i64),
    Foo(i64),
    PrintString,
    Readline(String),
}
impl HostFunctionRet {
    pub(crate) fn into_vm(self, vm: &mut Vm) {
        match self {
            HostFunctionRet::Bar(out0, out1) => {
                (out0, out1).to_vm(vm);
            }
            HostFunctionRet::Foo(out) => {
                out.to_vm(vm);
            }
            HostFunctionRet::PrintString => {
                ().to_vm(vm);
            }
            HostFunctionRet::Readline(out) => {
                out.to_vm(vm);
            }
        }
        vm.clear_pending_host_func()
    }
}
