// This is an auto-generated file.

mod term;
pub mod ffi {
    pub mod term {
        use crate::term;
        use abra_core::addons::*;
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
            unsafe fn from_vm(vm: *mut Vm) -> Self {
                unsafe {
                    abra_vm_deconstruct(vm);
                    let tag = abra_vm_pop_int(vm);
                    match tag {
                        0 => {
                            abra_vm_pop_nil(vm);
                            KeyCode::Left
                        }
                        1 => {
                            abra_vm_pop_nil(vm);
                            KeyCode::Right
                        }
                        2 => {
                            abra_vm_pop_nil(vm);
                            KeyCode::Up
                        }
                        3 => {
                            abra_vm_pop_nil(vm);
                            KeyCode::Down
                        }
                        4 => {
                            let value: String = <String>::from_vm(vm);
                            KeyCode::Char(value)
                        }
                        5 => {
                            abra_vm_pop_nil(vm);
                            KeyCode::Esc
                        }
                        6 => {
                            abra_vm_pop_nil(vm);
                            KeyCode::Other
                        }
                        _ => panic!("unexpected tag encountered: {}", tag),
                    }
                }
            }
            unsafe fn to_vm(self, vm: *mut Vm) {
                unsafe {
                    match self {
                        KeyCode::Left => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 0);
                        }
                        KeyCode::Right => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 1);
                        }
                        KeyCode::Up => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 2);
                        }
                        KeyCode::Down => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 3);
                        }
                        KeyCode::Char(value) => {
                            value.to_vm(vm);
                            abra_vm_construct_variant(vm, 4);
                        }
                        KeyCode::Esc => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 5);
                        }
                        KeyCode::Other => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 6);
                        }
                    }
                }
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$enable_raw_mode")]
        pub unsafe extern "C" fn enable_raw_mode(vm: *mut Vm) {
            unsafe {
                let ret: () = term::enable_raw_mode();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$disable_raw_mode")]
        pub unsafe extern "C" fn disable_raw_mode(vm: *mut Vm) {
            unsafe {
                let ret: () = term::disable_raw_mode();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$poll_key_event")]
        pub unsafe extern "C" fn poll_key_event(vm: *mut Vm) {
            unsafe {
                let ret: bool = term::poll_key_event();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$get_key_event")]
        pub unsafe extern "C" fn get_key_event(vm: *mut Vm) {
            unsafe {
                let ret: KeyCode = term::get_key_event();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$clear")]
        pub unsafe extern "C" fn clear(vm: *mut Vm) {
            unsafe {
                let ret: () = term::clear();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$hide_cursor")]
        pub unsafe extern "C" fn hide_cursor(vm: *mut Vm) {
            unsafe {
                let ret: () = term::hide_cursor();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$show_cursor")]
        pub unsafe extern "C" fn show_cursor(vm: *mut Vm) {
            unsafe {
                let ret: () = term::show_cursor();
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$mark")]
        pub unsafe extern "C" fn mark(vm: *mut Vm) {
            unsafe {
                let y = i64::from_vm(vm);
                let x = i64::from_vm(vm);
                let s = String::from_vm(vm);
                let ret: () = term::mark(s, x, y);
                ret.to_vm(vm);
            }
        }
        /// # Safety: `vm` must be non-null and valid.
        #[unsafe(export_name = "abra_ffi$term$flush")]
        pub unsafe extern "C" fn flush(vm: *mut Vm) {
            unsafe {
                let ret: () = term::flush();
                ret.to_vm(vm);
            }
        }
    }
}
