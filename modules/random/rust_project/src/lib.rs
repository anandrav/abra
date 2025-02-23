// This is an auto-generated file.

mod random;
pub mod ffi {
    pub mod random {
        use crate::random;
        use abra_core::addons::*;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$random$random_float")]
        pub unsafe extern "C" fn random_float(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let max = f64::from_vm(vm, vm_funcs);
                let min = f64::from_vm(vm, vm_funcs);
                let ret: f64 = random::random_float(min, max);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$random$random_int")]
        pub unsafe extern "C" fn random_int(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let max = i64::from_vm(vm, vm_funcs);
                let min = i64::from_vm(vm, vm_funcs);
                let ret: i64 = random::random_int(min, max);
                ret.to_vm(vm, vm_funcs);
            }
        }
    }
}
