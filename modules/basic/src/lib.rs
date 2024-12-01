// use std::collections::HashMap;
// use std::ffi::{c_char, CString};
// use std::fs::File;
// use std::sync::LazyLock;

// use abra_core::{addons::*, vm::Vm};

// static mut FILES: LazyLock<HashMap<i64, File>> = LazyLock::new(|| HashMap::new());
// static mut FILE_COUNTER: i64 = 0;

// #[no_mangle]
// pub unsafe extern "C" fn add(vm: *mut Vm) {
//     let n1 = unsafe { vm_pop_int(vm) };
//     let n2 = unsafe { vm_pop_int(vm) };
//     let ret = n1 + n2;
//     unsafe { vm_push_int(vm, ret) };
// }

// #[no_mangle]
// pub unsafe extern "C" fn fopen(vm: *mut Vm) {
//     // TODO: make a macro for this called get_string!
//     let string_view = unsafe { vm_view_string(vm) };
//     let s = string_view.to_string();
//     unsafe { vm_pop(vm) };

//     let f = File::create(s).unwrap(); // TODO: remove unwrap. fopen should return an Option

//     // TODO: make function or macro for this
//     let f_id = FILE_COUNTER;
//     FILE_COUNTER += 1;

//     FILES.insert(f_id, f);

//     unsafe { vm_push_int(vm, f_id) };
// }

use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::sync::{LazyLock, Mutex};

use abra_core::{addons::*, vm::Vm};

// // Wrap the HashMap in a Mutex to allow mutation
// static FILES: LazyLock<Mutex<HashMap<i64, File>>> = LazyLock::new(|| Mutex::new(HashMap::new()));
// static mut FILE_COUNTER: i64 = 0;

#[no_mangle]
pub unsafe extern "C" fn add(vm: *mut Vm) {
    let n1 = vm_pop_int(vm);
    let n2 = vm_pop_int(vm);
    let ret = n1 + n2;
    vm_push_int(vm, ret);
}

// #[no_mangle]
// pub unsafe extern "C" fn fopen(vm: *mut Vm) {
//     // TODO: make a macro for this called get_string!
//     let string_view = vm_view_string(vm);
//     let s = string_view.to_owned();
//     vm_pop(vm);

//     let f = File::open(s).unwrap(); // TODO: remove unwrap. fopen should return an Option

//     // Safely lock the FILES map to insert the file
//     let f_id;
//     {
//         let mut files = FILES.lock().unwrap(); // TODO: remove unwrap
//         f_id = FILE_COUNTER;
//         FILE_COUNTER += 1;
//         files.insert(f_id, f);
//     }

//     vm_push_int(vm, f_id);
// }

#[no_mangle]
pub unsafe extern "C" fn fread(vm: *mut Vm) {
    // TODO: make a macro for this called get_string!
    let string_view = vm_view_string(vm);
    let s = string_view.to_owned();
    vm_pop(vm);

    let mut f = File::open(s).unwrap(); // TODO: remove unwrap. fopen should return an Option

    let mut buf = String::new();
    f.read_to_string(&mut buf).unwrap();

    let string_view = StringView::from_string(&buf);
    vm_push_string(vm, string_view);
}
