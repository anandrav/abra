/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// functions used for testing

use abra_core::vm::{AbraFloat, AbraInt, Value, Vm};
use abra_core::{ErrorSummary, MockFileProvider, compile_bytecode};
use std::fmt::Debug;

pub fn unwrap_or_panic<T>(result: Result<T, ErrorSummary>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => {
            panic!("{}", e.to_string_ansi());
        }
    }
}

pub trait ExpectedValue {
    fn get_from_vm(vm: &mut Vm, val: Value) -> Self;
}

impl ExpectedValue for AbraInt {
    fn get_from_vm(vm: &mut Vm, val: Value) -> AbraInt {
        val.get_int(vm)
    }
}

impl ExpectedValue for AbraFloat {
    fn get_from_vm(vm: &mut Vm, val: Value) -> AbraFloat {
        val.get_float(vm)
    }
}

impl ExpectedValue for bool {
    fn get_from_vm(vm: &mut Vm, val: Value) -> bool {
        val.get_bool(vm)
    }
}

impl ExpectedValue for String {
    fn get_from_vm(vm: &mut Vm, val: Value) -> String {
        val.view_string(vm).to_string()
    }
}

pub fn expect_value<T: Into<Value> + ExpectedValue + Eq + Debug>(src: &str, val: T) {
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    assert_eq!(T::get_from_vm(&mut vm, top), val);
}

pub fn should_fail(src: &str) {
    compile_bytecode("main.abra", MockFileProvider::single_file(src)).unwrap_err();
}
