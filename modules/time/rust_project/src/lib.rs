// This is an auto-generated file.

mod time;
pub mod ffi {
    pub mod time {
        use crate::time;
        use abra_core::addons::*;
        #[unsafe(export_name = "abra_ffi$time$get_time")]
        pub unsafe extern "C" fn get_time(vm: *mut Vm) {
            let ret: f64 = time::get_time();
            ret.to_vm(vm);
        }
        #[unsafe(export_name = "abra_ffi$time$sleep")]
        pub unsafe extern "C" fn sleep(vm: *mut Vm) {
            let seconds = f64::from_vm(vm);
            let ret: () = time::sleep(seconds);
            ret.to_vm(vm);
        }
    }
}
