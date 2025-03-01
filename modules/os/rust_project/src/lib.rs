// This is an auto-generated file.

mod os;
pub mod ffi {
    pub mod os {
        use crate::os;
        use abra_core::addons::*;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fread")]
        pub unsafe extern "C" fn fread(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: Result<String, String> = os::fread(path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fwrite")]
        pub unsafe extern "C" fn fwrite(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let contents = <String>::from_vm(vm, vm_funcs);
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: () = os::fwrite(path, contents);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fexists")]
        pub unsafe extern "C" fn fexists(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: bool = os::fexists(path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fremove")]
        pub unsafe extern "C" fn fremove(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: () = os::fremove(path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$frename")]
        pub unsafe extern "C" fn frename(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let new_path = <String>::from_vm(vm, vm_funcs);
                let old_path = <String>::from_vm(vm, vm_funcs);
                let ret: () = os::frename(old_path, new_path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fcopy")]
        pub unsafe extern "C" fn fcopy(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let dest = <String>::from_vm(vm, vm_funcs);
                let src = <String>::from_vm(vm, vm_funcs);
                let ret: () = os::fcopy(src, dest);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$os$fappend")]
        pub unsafe extern "C" fn fappend(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let contents = <String>::from_vm(vm, vm_funcs);
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: () = os::fappend(path, contents);
                ret.to_vm(vm, vm_funcs);
            }
        }
        pub mod exec {
            use crate::os::exec;
            use abra_core::addons::*;
            use std::ffi::c_void;
            /// # Safety
            /// `vm` must be non-null and valid.
            #[unsafe(export_name = "abra_ffi$os$exec$command")]
            pub unsafe extern "C" fn command(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
                unsafe {
                    let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                    let s = <String>::from_vm(vm, vm_funcs);
                    let ret: i64 = exec::command(s);
                    ret.to_vm(vm, vm_funcs);
                }
            }
        }
        pub mod env {
            use crate::os::env;
            use abra_core::addons::*;
            use std::ffi::c_void;
            /// # Safety
            /// `vm` must be non-null and valid.
            #[unsafe(export_name = "abra_ffi$os$env$get_var")]
            pub unsafe extern "C" fn get_var(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
                unsafe {
                    let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                    let key = <String>::from_vm(vm, vm_funcs);
                    let ret: String = env::get_var(key);
                    ret.to_vm(vm, vm_funcs);
                }
            }
        }
    }
}
