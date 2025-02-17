// This is an auto-generated file.

mod os;
pub mod ffi {
    pub mod os {
        use crate::os;
        use abra_core::addons::*;
        #[export_name = "abra_ffi$os$fread"]
        pub unsafe extern "C" fn fread(vm: *mut Vm) {
            let path = String::from_vm(vm);
            let ret: Result<String, String> = os::fread(path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$os$fwrite"]
        pub unsafe extern "C" fn fwrite(vm: *mut Vm) {
            let contents = String::from_vm(vm);
            let path = String::from_vm(vm);
            let ret: () = os::fwrite(path, contents);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$os$fexists"]
        pub unsafe extern "C" fn fexists(vm: *mut Vm) {
            let path = String::from_vm(vm);
            let ret: bool = os::fexists(path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$os$fremove"]
        pub unsafe extern "C" fn fremove(vm: *mut Vm) {
            let path = String::from_vm(vm);
            let ret: () = os::fremove(path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$os$frename"]
        pub unsafe extern "C" fn frename(vm: *mut Vm) {
            let new_path = String::from_vm(vm);
            let old_path = String::from_vm(vm);
            let ret: () = os::frename(old_path, new_path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$os$fcopy"]
        pub unsafe extern "C" fn fcopy(vm: *mut Vm) {
            let dest = String::from_vm(vm);
            let src = String::from_vm(vm);
            let ret: () = os::fcopy(src, dest);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$os$fappend"]
        pub unsafe extern "C" fn fappend(vm: *mut Vm) {
            let contents = String::from_vm(vm);
            let path = String::from_vm(vm);
            let ret: () = os::fappend(path, contents);
            ret.to_vm(vm);
        }
        pub mod time {
            use crate::os::time;
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
            #[export_name = "abra_ffi$os$time$get_time"]
            pub unsafe extern "C" fn get_time(vm: *mut Vm) {
                let ret: Time = time::get_time();
                ret.to_vm(vm);
            }
        }
        pub mod exec {
            use crate::os::exec;
            use abra_core::addons::*;
            #[export_name = "abra_ffi$os$exec$command"]
            pub unsafe extern "C" fn command(vm: *mut Vm) {
                let s = String::from_vm(vm);
                let ret: i64 = exec::command(s);
                ret.to_vm(vm);
            }
        }
        pub mod env {
            use crate::os::env;
            use abra_core::addons::*;
            #[export_name = "abra_ffi$os$env$get_var"]
            pub unsafe extern "C" fn get_var(vm: *mut Vm) {
                let key = String::from_vm(vm);
                let ret: String = env::get_var(key);
                ret.to_vm(vm);
            }
        }
    }
}
