/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{error::Error, path::PathBuf};

use abra_core::{
    OsFileProvider,
    vm::{Vm, VmStatus},
};
use host_funcs::HostFunction;

mod host_funcs;

fn main() -> Result<(), Box<dyn Error>> {
    let abra_src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("abra_src");
    let file_provider = OsFileProvider::new(abra_src_dir, PathBuf::new(), PathBuf::new());

    let program = abra_core::compile_bytecode("main.abra", file_provider)?;

    let mut vm = Vm::new(program);
    vm.run();
    let status = vm.status();
    let VmStatus::PendingHostFunc(i) = status else {
        panic!()
    };
    let HostFunction::Bar = i.into() else {
        panic!()
    };
    let a = vm.pop()?.get_int(&vm)?;
    let b = vm.pop()?.get_int(&vm)?;
    let ret = a + b;
    vm.push_int(ret);
    vm.clear_pending_host_func();
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 10);

    Ok(())
}
