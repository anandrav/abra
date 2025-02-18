// This is an auto-generated file.

mod term;
pub mod ffi {
    pub mod term {
        use crate::term;
        use abra_core::addons::*;
        #[export_name = "abra_ffi$term$fread"]
        pub unsafe extern "C" fn fread(vm: *mut Vm) {
            let path = String::from_vm(vm);
            let ret: Result<String, String> = term::fread(path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$fwrite"]
        pub unsafe extern "C" fn fwrite(vm: *mut Vm) {
            let contents = String::from_vm(vm);
            let path = String::from_vm(vm);
            let ret: () = term::fwrite(path, contents);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$fexists"]
        pub unsafe extern "C" fn fexists(vm: *mut Vm) {
            let path = String::from_vm(vm);
            let ret: bool = term::fexists(path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$fremove"]
        pub unsafe extern "C" fn fremove(vm: *mut Vm) {
            let path = String::from_vm(vm);
            let ret: () = term::fremove(path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$frename"]
        pub unsafe extern "C" fn frename(vm: *mut Vm) {
            let new_path = String::from_vm(vm);
            let old_path = String::from_vm(vm);
            let ret: () = term::frename(old_path, new_path);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$fcopy"]
        pub unsafe extern "C" fn fcopy(vm: *mut Vm) {
            let dest = String::from_vm(vm);
            let src = String::from_vm(vm);
            let ret: () = term::fcopy(src, dest);
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$fappend"]
        pub unsafe extern "C" fn fappend(vm: *mut Vm) {
            let contents = String::from_vm(vm);
            let path = String::from_vm(vm);
            let ret: () = term::fappend(path, contents);
            ret.to_vm(vm);
        }
    }
}
