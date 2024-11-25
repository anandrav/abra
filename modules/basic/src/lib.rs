extern crate abra_core;

use abra_core::{addons::*, vm::Vm};

#[no_mangle]
pub extern "C" fn addon_description() -> *const AddonDesc {
    println!("helloooo");

    static DESC: AddonDesc = AddonDesc {
        name: "basic",
        funcs: &[FuncDesc {
            name: "add",
            arg_types: &[Type::Int, Type::Int],
            ret_type: Type::Int,
            func: |vm: &mut Vm| {
                let n1 = vm.top().get_int();
                vm.pop();
                let n2 = vm.top().get_int();
                vm.pop();

                let ret = add(n1, n2);
                vm.push_int(ret);
            },
        }],
    };
    &DESC
}

fn add(n1: i64, n2: i64) -> i64 {
    n1 + n2
}
