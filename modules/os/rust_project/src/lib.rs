// This is an auto-generated file.

mod os;
pub mod ffi {
    pub mod os {
        use crate::os;
        use abra_core::addons::*;
        #[allow(unused)]
        use abra_core::vm::AbraInt;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fread")]
        pub unsafe extern "C" fn fread(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: Option<String> = os::fread(path);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fwrite")]
        pub unsafe extern "C" fn fwrite(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let contents = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                os::fwrite(path, contents);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fexists")]
        pub unsafe extern "C" fn fexists(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: bool = os::fexists(path);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fremove")]
        pub unsafe extern "C" fn fremove(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                os::fremove(path);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$frename")]
        pub unsafe extern "C" fn frename(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let new_path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let old_path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                os::frename(old_path, new_path);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fcopy")]
        pub unsafe extern "C" fn fcopy(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let dest = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let src = <String>::from_vm_unsafe(_vm, _vm_funcs);
                os::fcopy(src, dest);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fappend")]
        pub unsafe extern "C" fn fappend(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let contents = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let path = <String>::from_vm_unsafe(_vm, _vm_funcs);
                os::fappend(path, contents);
            }
        }
        pub mod exec {
            use crate::os::exec;
            use abra_core::addons::*;
            #[allow(unused)]
            use abra_core::vm::AbraInt;
            use std::ffi::c_void;
            /// # Safety
            /// `vm` must be non-null and valid.
            #[unsafe(export_name = "abra_ffi$os$exec$command")]
            pub unsafe extern "C" fn command(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
                unsafe {
                    let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                    let s = <String>::from_vm_unsafe(_vm, _vm_funcs);
                    let ret: AbraInt = exec::command(s);
                    ret.to_vm_unsafe(_vm, _vm_funcs);
                }
            }
        }
        pub mod env {
            use crate::os::env;
            use abra_core::addons::*;
            #[allow(unused)]
            use abra_core::vm::AbraInt;
            use std::ffi::c_void;
            /// # Safety
            /// `vm` must be non-null and valid.
            #[unsafe(export_name = "abra_ffi$os$env$get_var")]
            pub unsafe extern "C" fn get_var(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
                unsafe {
                    let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                    let key = <String>::from_vm_unsafe(_vm, _vm_funcs);
                    let ret: String = env::get_var(key);
                    ret.to_vm_unsafe(_vm, _vm_funcs);
                }
            }
        }
    }
}
