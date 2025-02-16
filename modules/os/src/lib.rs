use abra_core::addons::*;
use abra_core::vm::Vm;
use std::fs;

// submodules
mod exec;

#[export_name = "abra_ffi$os$fread"]
pub unsafe extern "C" fn fread(vm: *mut Vm) {
    // define the implementation of "os.abra" in this file
    #[path = "../os.rs"]
    mod os;

    // TODO: make a macro for this called get_string!
    let string_view = abra_vm_view_string(vm);
    let path = string_view.to_owned();
    abra_vm_pop(vm);

    let content = os::fread(path);

    let string_view = StringView::from_string(&content);
    abra_vm_push_string(vm, string_view);
}

#[export_name = "abra_ffi$os$fwrite"]
pub unsafe extern "C" fn fwrite(vm: *mut Vm) {
    // define the implementation of "os.abra" in this file
    #[path = "../os.rs"]
    mod os;

    let string_view = abra_vm_view_string(vm);
    let content = string_view.to_owned();
    abra_vm_pop(vm);

    // TODO: make a macro for this called get_string!
    let string_view = abra_vm_view_string(vm);
    let path = string_view.to_owned();
    abra_vm_pop(vm);

    os::fwrite(path, content);

    abra_vm_push_nil(vm);
}

#[export_name = "abra_ffi$os$exec$command"]
pub unsafe extern "C" fn command(vm: *mut Vm) {
    // define the implementation of "os.abra" in this file
    // #[path = "exec.rs"] // TODO path necessary here?
    // mod exec;

    let string_view = abra_vm_view_string(vm);
    let content = string_view.to_owned();
    abra_vm_pop(vm);

    let ret = exec::command(content);

    abra_vm_push_int(vm, ret);
}
