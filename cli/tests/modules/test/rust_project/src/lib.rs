// This is an auto-generated file.

mod test;
pub mod ffi {
    pub mod test {
        use crate::test;
        use abra_core::addons::*;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$fread")]
        pub unsafe extern "C" fn fread(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: Result<String, String> = test::fread(path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$fwrite")]
        pub unsafe extern "C" fn fwrite(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let contents = <String>::from_vm(vm, vm_funcs);
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: () = test::fwrite(path, contents);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$fexists")]
        pub unsafe extern "C" fn fexists(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: bool = test::fexists(path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$fremove")]
        pub unsafe extern "C" fn fremove(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: () = test::fremove(path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$frename")]
        pub unsafe extern "C" fn frename(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let new_path = <String>::from_vm(vm, vm_funcs);
                let old_path = <String>::from_vm(vm, vm_funcs);
                let ret: () = test::frename(old_path, new_path);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$fcopy")]
        pub unsafe extern "C" fn fcopy(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let dest = <String>::from_vm(vm, vm_funcs);
                let src = <String>::from_vm(vm, vm_funcs);
                let ret: () = test::fcopy(src, dest);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test$fappend")]
        pub unsafe extern "C" fn fappend(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let contents = <String>::from_vm(vm, vm_funcs);
                let path = <String>::from_vm(vm, vm_funcs);
                let ret: () = test::fappend(path, contents);
                ret.to_vm(vm, vm_funcs);
            }
        }
        pub struct MyStruct {
            pub i: i64,
            pub b: bool,
            pub v: (),
            pub s: String,
        }
        impl VmType for MyStruct {
            unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                unsafe {
                    (vm_funcs.deconstruct)(vm);
                    let s = <String>::from_vm(vm, vm_funcs);
                    let v = <()>::from_vm(vm, vm_funcs);
                    let b = <bool>::from_vm(vm, vm_funcs);
                    let i = <i64>::from_vm(vm, vm_funcs);
                    Self { i, b, v, s }
                }
            }
            unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                unsafe {
                    self.i.to_vm(vm, vm_funcs);
                    self.b.to_vm(vm, vm_funcs);
                    self.v.to_vm(vm, vm_funcs);
                    self.s.to_vm(vm, vm_funcs);
                    (vm_funcs.construct)(vm, 4);
                }
            }
        }
        pub enum MyEnum {
            Int(i64),
            Bool(bool),
            Void,
            String(String),
        }
        impl VmType for MyEnum {
            unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                unsafe {
                    (vm_funcs.deconstruct)(vm);
                    let tag = (vm_funcs.pop_int)(vm);
                    match tag {
                        0 => {
                            let value: i64 = <i64>::from_vm(vm, vm_funcs);
                            MyEnum::Int(value)
                        }
                        1 => {
                            let value: bool = <bool>::from_vm(vm, vm_funcs);
                            MyEnum::Bool(value)
                        }
                        2 => {
                            (vm_funcs.pop_nil)(vm);
                            MyEnum::Void
                        }
                        3 => {
                            let value: String = <String>::from_vm(vm, vm_funcs);
                            MyEnum::String(value)
                        }
                        _ => panic!("unexpected tag encountered: {}", tag),
                    }
                }
            }
            unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                unsafe {
                    match self {
                        MyEnum::Int(value) => {
                            value.to_vm(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 0);
                        }
                        MyEnum::Bool(value) => {
                            value.to_vm(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 1);
                        }
                        MyEnum::Void => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 2);
                        }
                        MyEnum::String(value) => {
                            value.to_vm(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 3);
                        }
                    }
                }
            }
        }
    }
}
