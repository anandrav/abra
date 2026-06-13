/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{error::Error, path::PathBuf};

use abra_core::vm::{Runtime, RuntimeStatus};
use abra_core::{OsFileProvider, vm::VmStatus};

mod generated;
use generated::*;

fn main() -> Result<(), Box<dyn Error>> {
    let abra_src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR")?).join("abra_src");
    let file_provider = OsFileProvider::single_dir(abra_src_dir);

    let program = abra_core::compile_bytecode("main.abra", file_provider)?;

    let mut runtime = Runtime::new(program);
    for _ in 0..4 {
        let status = runtime.run();
        handle_host_func(&mut runtime, status);
    }
    runtime.run();
    let top = runtime.top();
    // 28 (from before) + 30 (p.age) + 42 (bl.n) = 100
    assert_eq!(top.get_int(runtime.main_mut()), 100);

    // prevent warning for unused Color type (not yet tested via host functions)
    let _ = Color::Red;

    Ok(())
}

fn handle_host_func(runtime: &mut Runtime, status: RuntimeStatus) {
    let RuntimeStatus::PendingHostFunc = status else { panic!() };
    for thread in runtime.iter_threads_mut() {
        let status = thread.status();
        let VmStatus::PendingHostFunc(i) = status else { continue };
        let host_func_args: HostFunctionArgs = HostFunctionArgs::from_vm(thread, i);

        // TODO: flesh this out a bit more.
        // test single argument, multiple argument, no arguments
        // test void return value, single return value, tuple return value
        match host_func_args {
            HostFunctionArgs::PrintString(_s) => {
                let _ = HostFunctionRet::PrintString;
                panic!()
            }
            HostFunctionArgs::EprintString(_s) => {
                let _ = HostFunctionRet::EprintString;
                panic!()
            }
            HostFunctionArgs::Readline => {
                let _ = HostFunctionRet::Readline("".into());
                panic!()
            }
            HostFunctionArgs::GetArgs => {
                let _ = HostFunctionRet::GetArgs(vec![]);
                panic!()
            }
            HostFunctionArgs::Foo(_n, _s) => {
                let _ = HostFunctionRet::Foo(0);
                panic!()
            }
            HostFunctionArgs::Bar(n1, n2) => {
                HostFunctionRet::Bar(n1 * 2, n2 * 2).into_vm(thread);
            }
            HostFunctionArgs::MakePerson(name, age) => {
                HostFunctionRet::MakePerson(Person { name, age }).into_vm(thread);
            }
            HostFunctionArgs::GetBlah => {
                HostFunctionRet::GetBlah(Blah { n: 42 }).into_vm(thread);
            }
        }
    }
}
