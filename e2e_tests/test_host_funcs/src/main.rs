/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{error::Error, path::PathBuf};

use abra_core::vm::Value;
use abra_core::{
    OsFileProvider,
    vm::{Vm, VmStatus},
};
use host_funcs::*;

mod host_funcs;

fn main() -> Result<(), Box<dyn Error>> {
    let abra_src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("abra_src");
    let file_provider = OsFileProvider::new(abra_src_dir, PathBuf::new(), PathBuf::new());

    let program = abra_core::compile_bytecode("main.abra", file_provider)?;

    let mut vm = Vm::new(program);
    vm.run();
    let status = vm.status();
    let VmStatus::PendingHostFunc(i) = status else { panic!() };
    let host_func_args: HostFunctionArgs = HostFunctionArgs::from_vm(&mut vm, i);
    // TODO: flesh this out a bit more.
    // test single argument, multiple argument, no arguments
    // test void return value, single return value, tuple return value
    match host_func_args {
        HostFunctionArgs::PrintString(_s) => {
            let _ = HostFunctionRet::PrintString;
            panic!()
        }
        HostFunctionArgs::Readline => {
            let _ = HostFunctionRet::Readline("".into());
            panic!()
        }
        HostFunctionArgs::Foo(_n, _s) => {
            let _ = HostFunctionRet::Foo(0);
            panic!()
        }
        HostFunctionArgs::Bar(n1, n2) => {
            HostFunctionRet::Bar(n1 * 2, n2 * 2).into_vm(&mut vm);
        }
    }
    let _ = Color::Red;
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 10);

    Ok(())
}
