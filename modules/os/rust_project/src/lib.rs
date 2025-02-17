mod os;

pub mod ffi {
    pub mod os {
        use crate::os;
        use abra_core::addons::*;

        #[export_name = "abra_ffi$os$fread"]
        pub unsafe extern "C" fn fread(vm: *mut Vm) {
            let string_view = abra_vm_view_string(vm);
            let path = string_view.to_owned();
            abra_vm_pop(vm);

            let ret = os::fread(path);

            let string_view = StringView::from_string(&ret);
            abra_vm_push_string(vm, string_view);
        }

        #[export_name = "abra_ffi$os$fwrite"]
        pub unsafe extern "C" fn fwrite(vm: *mut Vm) {
            let string_view = abra_vm_view_string(vm);
            let content = string_view.to_owned();
            abra_vm_pop(vm);

            let string_view = abra_vm_view_string(vm);
            let path = string_view.to_owned();
            abra_vm_pop(vm);

            os::fwrite(path, content);

            abra_vm_push_nil(vm);
        }

        pub mod exec {
            use crate::os::exec;
            use abra_core::addons::*;

            #[export_name = "abra_ffi$os$exec$command"]
            pub unsafe extern "C" fn command(vm: *mut Vm) {
                let string_view = abra_vm_view_string(vm);
                let content = string_view.to_owned();
                abra_vm_pop(vm);

                let ret = exec::command(content);

                abra_vm_push_int(vm, ret);
            }
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
                        let nanoseconds = abra_vm_pop_int(vm);
                        let seconds = abra_vm_pop_int(vm);
                        Self {
                            seconds,
                            nanoseconds,
                        }
                    }
                }

                unsafe fn to_vm(self, vm: *mut Vm) {
                    unsafe {
                        abra_vm_push_int(vm, self.seconds);
                        abra_vm_push_int(vm, self.nanoseconds);
                        abra_vm_construct(vm, 2);
                    }
                }
            }

            #[export_name = "abra_ffi$os$time$get_time"]
            pub unsafe extern "C" fn get_time(vm: *mut Vm) {
                let ret = time::get_time();

                ret.to_vm(vm);
            }
        }
    }
}
