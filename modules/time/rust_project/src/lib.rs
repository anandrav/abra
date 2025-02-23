// This is an auto-generated file.

mod time;
pub mod ffi {
    pub mod time {
        use crate::time;
        use abra_core::addons::*;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$time$get_time")]
        pub unsafe extern "C" fn get_time(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: f64 = time::get_time();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$time$sleep")]
        pub unsafe extern "C" fn sleep(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let seconds = f64::from_vm(vm, vm_funcs);
                let ret: () = time::sleep(seconds);
                ret.to_vm(vm, vm_funcs);
            }
        }
    }
}
