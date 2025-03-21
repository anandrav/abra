use std::{collections::HashMap, error::Error, path::PathBuf};

use abra_core::{
    MockFileProvider,
    effects::{DefaultEffects, EffectTrait},
    vm::{Vm, VmStatus},
};
use host_funcs::HostFunction;
use test_host_funcs_helper::*;

mod host_funcs;

fn main() -> Result<(), Box<dyn Error>> {
    let mut files: HashMap<PathBuf, String> = HashMap::new();
    files.insert("main.abra".into(), MAIN_ABRA.into());
    files.insert("util.abra".into(), UTIL_ABRA.into());
    let file_provider = MockFileProvider::new(files);

    let program =
        abra_core::compile_bytecode("main.abra", DefaultEffects::enumerate(), file_provider)?;

    let mut vm = Vm::new(program);
    vm.run();
    let status = vm.status();
    let VmStatus::PendingEffect(i) = status else {
        panic!()
    };
    let HostFunction::foo = i.into() else {
        panic!()
    };
    let a = vm.pop()?.get_int(&vm)?;
    let b = vm.pop()?.get_int(&vm)?;
    let ret = a + b;
    vm.push_int(ret);
    vm.clear_pending_effect();
    vm.run();
    let top = vm.top().unwrap();
    assert_eq!(top.get_int(&vm).unwrap(), 10);

    Ok(())
}
