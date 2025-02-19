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
                            abra_vm_construct_variant(vm, 0);
                        }
                        KeyCode::Up => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 0);
                        }
                        KeyCode::Down => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 0);
                        }
                        KeyCode::Char(value) => {
                            value.to_vm(vm);
                            abra_vm_construct_variant(vm, 4);
                        }
                        KeyCode::Esc => {
                            abra_vm_push_nil(vm);
                            abra_vm_construct_variant(vm, 0);
                        }
                    }
                }
            }
        }
        #[export_name = "abra_ffi$term$poll_key_event"]
        pub unsafe extern "C" fn poll_key_event(vm: *mut Vm) {
            let ret: bool = term::poll_key_event();
            ret.to_vm(vm);
        }
        #[export_name = "abra_ffi$term$get_key_event"]
        pub unsafe extern "C" fn get_key_event(vm: *mut Vm) {
            let ret: KeyCode = term::get_key_event();
            ret.to_vm(vm);
        }
    }
}
