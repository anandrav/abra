extern crate abra_core;

use std::ffi::{c_char, CString};

use abra_core::{addons::*, vm::Vm};

#[no_mangle]
pub extern "C" fn addon_description() -> *const AddonDesc {
    println!("helloooo");

    const ADD_NAME: &str = "add";
    const ADDON_NAME: &str = "basic";

    let desc: AddonDesc = AddonDesc {
        name: ADDON_NAME,
        funcs: Array {
            ptr: &[FuncDesc {
                name: ADD_NAME,
                arg_types: Array {
                    ptr: &[Type::Int, Type::Int] as *const Type,
                    len: 2,
                },
                ret_type: Type::Int,
                func: |vm: &mut Vm| {
                    let n1 = vm.top().get_int();
                    vm.pop();
                    let n2 = vm.top().get_int();
                    vm.pop();

                    let ret = add(n1, n2);
                    vm.push_int(ret);
                },
            }] as *const FuncDesc,
            len: 1,
        },
    };
    &desc
}

fn add(n1: i64, n2: i64) -> i64 {
    n1 + n2
}
