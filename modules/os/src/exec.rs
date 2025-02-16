use std::process::Command;

use abra_core::addons::*;
use abra_core::vm::Vm;

#[no_mangle]
pub unsafe extern "C" fn command(vm: *mut Vm) {
    let string_view = abra_vm_view_string(vm);
    let content = string_view.to_owned();
    abra_vm_pop(vm);

    let content_elems: Vec<_> = content.split(' ').collect();

    let mut cmd = Command::new(content_elems[0]);
    for elem in &content_elems[1..] {
        cmd.arg(elem);
    }

    let output = cmd.output();
    let ret = match output {
        Ok(output) => {
            print!("{}", String::from_utf8_lossy(&output.stdout));
            eprint!("{}", String::from_utf8_lossy(&output.stderr));
            0
        }
        Err(err) => err.raw_os_error().unwrap() as i64,
    };
    abra_vm_push_int(vm, 0);
}
