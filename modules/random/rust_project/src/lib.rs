// This is an auto-generated file.

mod random;
pub mod ffi {
    pub mod random {
        use crate::random;
        use abra_core::addons::*;
        #[allow(unused)]
        use abra_core::vm::AbraInt;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$random$random_float")]
        pub unsafe extern "C" fn random_float(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let max = <f64>::from_vm_unsafe(_vm, _vm_funcs);
                let min = <f64>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: f64 = random::random_float(min, max);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$random$random_int")]
        pub unsafe extern "C" fn random_int(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let max = <AbraInt>::from_vm_unsafe(_vm, _vm_funcs);
                let min = <AbraInt>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: AbraInt = random::random_int(min, max);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
    }
}
