// This is an auto-generated file.

mod time;
pub mod ffi {
    pub mod time {
        use crate::time;
        use abra_core::addons::*;
        pub struct Time {
            pub seconds: i64,
            pub nanoseconds: i64,
        }
        impl VmType for Time {
            unsafe fn from_vm(vm: *mut Vm) -> Self {
                unsafe {
                    abra_vm_deconstruct(vm);
                    let nanoseconds = i64::from_vm(vm);
                    let seconds = i64::from_vm(vm);
                    Self {
                        seconds,
                        nanoseconds,
                    }
                }
            }
            unsafe fn to_vm(self, vm: *mut Vm) {
                unsafe {
                    self.seconds.to_vm(vm);
                    self.nanoseconds.to_vm(vm);
                    abra_vm_construct(vm, 2);
                }
            }
        }
        #[unsafe(export_name = "abra_ffi$time$get_time")]
        pub unsafe extern "C" fn get_time(vm: *mut Vm) { unsafe {
            let ret: Time = time::get_time();
            ret.to_vm(vm);
        }}
    }
}
