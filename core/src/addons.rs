// Rust addon API

use core::str;
use std::{
    ffi::c_char,
    fs,
    path::{Path, PathBuf},
};

pub use crate::vm::Vm;

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_push_int(vm: *mut Vm, n: i64) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.push_int(n);
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_push_nil(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.push_nil();
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_pop_int(vm: *mut Vm) -> i64 {
    let vm = unsafe { vm.as_mut().unwrap() };
    let top = vm.top().get_int();
    vm.pop();
    top
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_pop(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.pop();
}

#[repr(C)]
pub struct StringView {
    pub ptr: *const c_char,
    pub len: usize,
}

impl StringView {
    pub fn to_owned(self) -> String {
        unsafe {
            let byte_slice = std::slice::from_raw_parts(self.ptr as *const u8, self.len);
            str::from_utf8(byte_slice).unwrap().to_string()
        }
    }

    pub fn from_string(s: &str) -> Self {
        StringView {
            ptr: s.as_ptr() as *const c_char,
            len: s.len(),
        }
    }
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_view_string(vm: *mut Vm) -> StringView {
    let vm = unsafe { vm.as_mut().unwrap() };
    let top = vm.top().view_string(vm);
    StringView {
        ptr: top.as_ptr() as *const c_char,
        len: top.len(),
    }
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_push_string(vm: *mut Vm, string_view: StringView) {
    let vm = unsafe { vm.as_mut().unwrap() };
    let s = string_view.to_owned();
    vm.push_str(s);
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_construct(vm: *mut Vm, arity: u16) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.construct_struct(arity);
}

/// # Safety
/// vm: *mut Vm must be valid and non-null
#[no_mangle]
pub unsafe extern "C" fn abra_vm_deconstruct(vm: *mut Vm) {
    let vm = unsafe { vm.as_mut().unwrap() };
    vm.deconstruct();
}

use std::env::current_dir;

pub fn generate() {
    let current_dir = current_dir().unwrap();
    let mut package_dir = current_dir.clone();
    package_dir.pop();
    let package_name = package_dir
        .file_name()
        .unwrap()
        .to_str()
        .unwrap()
        .to_string();
    let mut toplevel_abra_file = package_dir.clone();
    toplevel_abra_file.pop();
    toplevel_abra_file = toplevel_abra_file.join(format!("{}.abra", package_name));

    let mut files = vec![toplevel_abra_file.clone()];

    find_abra_files(&package_dir, &mut files).unwrap();

    let mut output = String::new();
    output.push_str(
        r#"use abra_core::addons::*;
use abra_core::vm::Vm;"#,
    );
    output.push_str(&format!("mod {}", package_name));

    // panic!("toplevel abra file = {}", toplevel_abra_file.display());
}

fn find_abra_files(dir: &Path, files: &mut Vec<PathBuf>) -> std::io::Result<()> {
    for entry in fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            // Recursively search this directory.
            find_abra_files(&path, files)?;
        } else if let Some(ext) = path.extension() {
            // Check if the extension is "abra".
            if ext == "abra" {
                files.push(path);
            }
        }
    }
    Ok(())
}
