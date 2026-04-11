/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// functions used for testing

use abra_core::vm::{AbraFloat, AbraInt, Value, Vm};
use abra_core::{ErrorSummary, MockFileProvider, compile_bytecode};

pub fn unwrap_or_panic<T>(result: Result<T, ErrorSummary>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => {
            panic!("{}", e.to_string_ansi());
        }
    }
}

pub trait ExpectedValue {
    fn check(self, vm: &mut Vm, val: Value);
}

impl ExpectedValue for AbraInt {
    fn check(self, vm: &mut Vm, val: Value) {
        assert_eq!(val.get_int(vm), self);
    }
}

impl ExpectedValue for AbraFloat {
    fn check(self, vm: &mut Vm, val: Value) {
        assert_eq!(val.get_float(vm), self);
    }
}

impl ExpectedValue for bool {
    fn check(self, vm: &mut Vm, val: Value) {
        assert_eq!(val.get_bool(vm), self);
    }
}

impl ExpectedValue for &str {
    fn check(self, vm: &mut Vm, val: Value) {
        assert_eq!(val.view_string(vm), self);
    }
}

pub fn expect_value<T: ExpectedValue>(src: &str, val: T) {
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut vm = Vm::new(program);
    vm.run();
    let top = vm.top();
    val.check(&mut vm, top);
}

pub fn should_fail(src: &str) {
    compile_bytecode("main.abra", MockFileProvider::single_file(src)).unwrap_err();
}
