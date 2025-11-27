// This is an auto-generated file.

mod test_ffi;
pub mod ffi {
    pub mod test_ffi {
        use crate::test_ffi;
        use abra_core::addons::*;
        #[allow(unused)]
        use abra_core::vm::AbraInt;
        use std::ffi::c_void;
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_int")]
        pub unsafe extern "C" fn pass_int(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let i = <AbraInt>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: AbraInt = test_ffi::pass_int(i);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_bool")]
        pub unsafe extern "C" fn pass_bool(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let i = <bool>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: bool = test_ffi::pass_bool(i);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_void")]
        pub unsafe extern "C" fn pass_void(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                test_ffi::pass_void(());
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_string")]
        pub unsafe extern "C" fn pass_string(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let s = <String>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: String = test_ffi::pass_string(s);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_struct")]
        pub unsafe extern "C" fn pass_struct(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let s = <MyStruct>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: MyStruct = test_ffi::pass_struct(s);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_enum")]
        pub unsafe extern "C" fn pass_enum(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let e = <MyEnum>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: MyEnum = test_ffi::pass_enum(e);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_tuple")]
        pub unsafe extern "C" fn pass_tuple(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let e = <(bool, AbraInt, String)>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: (bool, AbraInt, String) = test_ffi::pass_tuple(e);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_option")]
        pub unsafe extern "C" fn pass_option(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let o = <Option<String>>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: Option<String> = test_ffi::pass_option(o);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$test_ffi$pass_array")]
        pub unsafe extern "C" fn pass_array(_vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let _vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let a = <Vec<AbraInt>>::from_vm_unsafe(_vm, _vm_funcs);
                let ret: Vec<AbraInt> = test_ffi::pass_array(a);
                ret.to_vm_unsafe(_vm, _vm_funcs);
            }
        }
        pub struct MyStruct {
            pub i: AbraInt,
            pub b: bool,
            pub v: (),
            pub s: String,
        }
        impl VmFfiType for MyStruct {
            unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                unsafe {
                    (vm_funcs.deconstruct_struct)(vm);
                    let i = <AbraInt>::from_vm_unsafe(vm, vm_funcs);
                    let b = <bool>::from_vm_unsafe(vm, vm_funcs);
                    let s = <String>::from_vm_unsafe(vm, vm_funcs);
                    Self { i, b, v: (), s }
                }
            }
            unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                unsafe {
                    self.i.to_vm_unsafe(vm, vm_funcs);
                    self.b.to_vm_unsafe(vm, vm_funcs);
                    self.s.to_vm_unsafe(vm, vm_funcs);
                    (vm_funcs.construct_struct)(vm, 3);
                }
            }
        }
        pub enum MyEnum {
            Int(AbraInt),
            Bool(bool),
            Void,
            AnotherVoid(()),
            String(String),
        }
        impl VmFfiType for MyEnum {
            unsafe fn from_vm_unsafe(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                unsafe {
                    (vm_funcs.deconstruct_variant)(vm);
                    let tag = (vm_funcs.pop_int)(vm);
                    match tag {
                        0 => {
                            let value: AbraInt = <AbraInt>::from_vm_unsafe(vm, vm_funcs);
                            MyEnum::Int(value)
                        }
                        1 => {
                            let value: bool = <bool>::from_vm_unsafe(vm, vm_funcs);
                            MyEnum::Bool(value)
                        }
                        2 => {
                            (vm_funcs.pop)(vm);
                            MyEnum::Void
                        }
                        3 => {
                            (vm_funcs.pop)(vm);
                            MyEnum::AnotherVoid(())
                        }
                        4 => {
                            let value: String = <String>::from_vm_unsafe(vm, vm_funcs);
                            MyEnum::String(value)
                        }
                        _ => panic!("unexpected tag encountered: {tag}"),
                    }
                }
            }
            unsafe fn to_vm_unsafe(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                unsafe {
                    match self {
                        MyEnum::Int(value) => {
                            value.to_vm_unsafe(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 0);
                        }
                        MyEnum::Bool(value) => {
                            value.to_vm_unsafe(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 1);
                        }
                        MyEnum::Void => {
                            (vm_funcs.push_int)(vm, 0);
                            (vm_funcs.construct_variant)(vm, 2);
                        }
                        MyEnum::AnotherVoid(()) => {
                            0.to_vm_unsafe(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 3);
                        }
                        MyEnum::String(value) => {
                            value.to_vm_unsafe(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 4);
                        }
                    }
                }
            }
        }
    }
}
