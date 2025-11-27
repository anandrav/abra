// This is an auto-generated file.

mod strings;
pub mod ffi {
    pub mod strings {
        use crate::strings;
        use abra_core::addons::*;
        #[allow(unused)]
        use abra_core::vm::AbraInt;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$strings$string_to_upper")]
        pub unsafe extern "C" fn string_to_upper(
            _vm: *mut c_void,
            vm_funcs: *const AbraVmFunctions,
        ) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let s = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: String = strings::string_to_upper(s);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$strings$string_to_lower")]
        pub unsafe extern "C" fn string_to_lower(
            _vm: *mut c_void,
            vm_funcs: *const AbraVmFunctions,
        ) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let s = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: String = strings::string_to_lower(s);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
    }
}
