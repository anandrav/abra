// This is an auto-generated file.

mod test_ffi;
pub mod ffi {
    pub mod test_ffi {
        use crate::test_ffi;
        use abra_core::addons::*;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_int")]
        pub unsafe extern "C" fn pass_int(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let i = <i64>::from_vm(vm, vm_funcs);
                let ret: i64 = test_ffi::pass_int(i);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_bool")]
        pub unsafe extern "C" fn pass_bool(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let i = <bool>::from_vm(vm, vm_funcs);
                let ret: bool = test_ffi::pass_bool(i);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_void")]
        pub unsafe extern "C" fn pass_void(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                (vm_funcs.pop_nil)(vm);
                let ret: () = test_ffi::pass_void(());
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_string")]
        pub unsafe extern "C" fn pass_string(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let s = <String>::from_vm(vm, vm_funcs);
                let ret: String = test_ffi::pass_string(s);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_struct")]
        pub unsafe extern "C" fn pass_struct(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let s = <MyStruct>::from_vm(vm, vm_funcs);
                let ret: MyStruct = test_ffi::pass_struct(s);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_enum")]
        pub unsafe extern "C" fn pass_enum(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let e = <MyEnum>::from_vm(vm, vm_funcs);
                let ret: MyEnum = test_ffi::pass_enum(e);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_tuple")]
        pub unsafe extern "C" fn pass_tuple(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let e = <(bool, i64, String)>::from_vm(vm, vm_funcs);
                let ret: (bool, i64, String) = test_ffi::pass_tuple(e);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_maybe")]
        pub unsafe extern "C" fn pass_maybe(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let m = <Result<String, i64>>::from_vm(vm, vm_funcs);
                let ret: Result<String, i64> = test_ffi::pass_maybe(m);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_array")]
        pub unsafe extern "C" fn pass_array(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let a = <Vec<i64>>::from_vm(vm, vm_funcs);
                let ret: Vec<i64> = test_ffi::pass_array(a);
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
                    let i = <i64>::from_vm(vm, vm_funcs);
                    let b = <bool>::from_vm(vm, vm_funcs);
                    (vm_funcs.pop_nil)(vm);
                    let s = <String>::from_vm(vm, vm_funcs);
                    Self { i, b, v: (), s }
                }
            }
            unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                unsafe {
                    self.i.to_vm(vm, vm_funcs);
                    self.b.to_vm(vm, vm_funcs);
                    (vm_funcs.push_nil)(vm);
                    self.s.to_vm(vm, vm_funcs);
                    (vm_funcs.construct_struct)(vm, 4);
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
                        _ => panic!("unexpected tag encountered: {tag}"),
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
