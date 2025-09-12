// This is an auto-generated file.

use abra_core::host::*;
use abra_core::vm::*;

#[allow(dead_code)]
pub enum HostFunction {
    PrintString,
    Readline,
}
impl From<u16> for HostFunction {
    fn from(item: u16) -> Self {
        match item {
            0 => HostFunction::PrintString,
            1 => HostFunction::Readline,
            i => panic!("unrecognized host func: {i}"),
        }
    }
}
pub enum HostFunctionArgs {
    PrintString(String),
    Readline,
}
impl HostFunctionArgs {
    pub(crate) fn from_vm(vm: &mut Vm, pending_host_func: u16) -> Self {
        match pending_host_func {
            0 => {
                let arg0: String = <String>::from_vm(vm);
                HostFunctionArgs::PrintString(arg0)
            }
            1 => HostFunctionArgs::Readline,
            _ => panic!("unexpected tag encountered: {pending_host_func}"),
        }
    }
}
pub enum HostFunctionRet {
    PrintString,
    Readline(String),
}
impl HostFunctionRet {
    pub(crate) fn into_vm(self, vm: &mut Vm) {
        match self {
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
