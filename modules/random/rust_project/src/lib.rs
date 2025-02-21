// This is an auto-generated file.

mod random;
pub mod ffi {
    pub mod random {
        use crate::random;
        use abra_core::addons::*;
        #[unsafe(export_name = "abra_ffi$random$random_float")]
        pub unsafe extern "C" fn random_float(vm: *mut Vm) {
            let max = f64::from_vm(vm);
            let min = f64::from_vm(vm);
            let ret: f64 = random::random_float(min, max);
            ret.to_vm(vm);
        }
        #[unsafe(export_name = "abra_ffi$random$random_int")]
        pub unsafe extern "C" fn random_int(vm: *mut Vm) {
            let max = i64::from_vm(vm);
            let min = i64::from_vm(vm);
            let ret: i64 = random::random_int(min, max);
            ret.to_vm(vm);
        }
    }
}
