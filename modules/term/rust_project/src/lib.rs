// This is an auto-generated file.

mod term;
pub mod ffi {
    pub mod term {
        use crate::term;
        use abra_core::addons::*;
        use std::ffi::c_void;
        pub enum KeyCode {
            Left,
            Right,
            Up,
            Down,
            Char(String),
            Esc,
            Other,
        }
        impl VmType for KeyCode {
            unsafe fn from_vm(vm: *mut c_void, vm_funcs: &AbraVmFunctions) -> Self {
                unsafe {
                    (vm_funcs.deconstruct)(vm);
                    let tag = (vm_funcs.pop_int)(vm);
                    match tag {
                        0 => {
                            (vm_funcs.pop_nil)(vm);
                            KeyCode::Left
                        }
                        1 => {
                            (vm_funcs.pop_nil)(vm);
                            KeyCode::Right
                        }
                        2 => {
                            (vm_funcs.pop_nil)(vm);
                            KeyCode::Up
                        }
                        3 => {
                            (vm_funcs.pop_nil)(vm);
                            KeyCode::Down
                        }
                        4 => {
                            let value: String = <String>::from_vm(vm, vm_funcs);
                            KeyCode::Char(value)
                        }
                        5 => {
                            (vm_funcs.pop_nil)(vm);
                            KeyCode::Esc
                        }
                        6 => {
                            (vm_funcs.pop_nil)(vm);
                            KeyCode::Other
                        }
                        _ => panic!("unexpected tag encountered: {tag}"),
                    }
                }
            }
            unsafe fn to_vm(self, vm: *mut c_void, vm_funcs: &AbraVmFunctions) {
                unsafe {
                    match self {
                        KeyCode::Left => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 0);
                        }
                        KeyCode::Right => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 1);
                        }
                        KeyCode::Up => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 2);
                        }
                        KeyCode::Down => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 3);
                        }
                        KeyCode::Char(value) => {
                            value.to_vm(vm, vm_funcs);
                            (vm_funcs.construct_variant)(vm, 4);
                        }
                        KeyCode::Esc => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 5);
                        }
                        KeyCode::Other => {
                            (vm_funcs.push_nil)(vm);
                            (vm_funcs.construct_variant)(vm, 6);
                        }
                    }
                }
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$enable_raw_mode")]
        pub unsafe extern "C" fn enable_raw_mode(
            vm: *mut c_void,
            vm_funcs: *const AbraVmFunctions,
        ) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: () = term::enable_raw_mode();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$disable_raw_mode")]
        pub unsafe extern "C" fn disable_raw_mode(
            vm: *mut c_void,
            vm_funcs: *const AbraVmFunctions,
        ) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: () = term::disable_raw_mode();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$poll_key_event")]
        pub unsafe extern "C" fn poll_key_event(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: bool = term::poll_key_event();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$get_key_event")]
        pub unsafe extern "C" fn get_key_event(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: KeyCode = term::get_key_event();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$clear")]
        pub unsafe extern "C" fn clear(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: () = term::clear();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$hide_cursor")]
        pub unsafe extern "C" fn hide_cursor(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: () = term::hide_cursor();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$show_cursor")]
        pub unsafe extern "C" fn show_cursor(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: () = term::show_cursor();
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$mark")]
        pub unsafe extern "C" fn mark(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let y = <i64>::from_vm(vm, vm_funcs);
                let x = <i64>::from_vm(vm, vm_funcs);
                let s = <String>::from_vm(vm, vm_funcs);
                let ret: () = term::mark(s, x, y);
                ret.to_vm(vm, vm_funcs);
            }
        }
        /// # Safety
        /// `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$flush")]
        pub unsafe extern "C" fn flush(vm: *mut c_void, vm_funcs: *const AbraVmFunctions) {
            unsafe {
                let vm_funcs: &AbraVmFunctions = &*vm_funcs;
                let ret: () = term::flush();
                ret.to_vm(vm, vm_funcs);
            }
        }
    }
}
