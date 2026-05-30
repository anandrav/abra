/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// functions used for testing

use abra_core::vm::{AbraFloat, AbraInt, Runtime, Value, Vm};
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
    fn check(self, runtime: &mut Runtime, val: Value);
}

impl ExpectedValue for AbraInt {
    fn check(self, runtime: &mut Runtime, val: Value) {
        assert_eq!(val.get_int(&runtime.thread), self);
    }
}

impl ExpectedValue for i32 {
    fn check(self, runtime: &mut Runtime, val: Value) {
        assert_eq!(val.get_int(&runtime.thread), self as AbraInt);
    }
}

impl ExpectedValue for AbraFloat {
    fn check(self, runtime: &mut Runtime, val: Value) {
        assert_eq!(val.get_float(&runtime.thread), self);
    }
}

impl ExpectedValue for f32 {
    fn check(self, runtime: &mut Runtime, val: Value) {
        assert_eq!(val.get_float(&runtime.thread), self as AbraFloat);
    }
}

impl ExpectedValue for bool {
    fn check(self, runtime: &mut Runtime, val: Value) {
        assert_eq!(val.get_bool(&runtime.thread), self);
    }
}

impl ExpectedValue for &str {
    fn check(self, runtime: &mut Runtime, val: Value) {
        assert_eq!(val.view_string(&runtime.thread), self);
    }
}

pub fn expect_value<T: ExpectedValue>(src: &str, val: T) {
    let program = unwrap_or_panic(compile_bytecode(
        "main.abra",
        MockFileProvider::single_file(src),
    ));
    let mut runtime = Runtime::new(program);
    runtime.run();
    let top = runtime.top();
    val.check(&mut runtime, top);
}

pub fn should_fail(src: &str) {
    compile_bytecode("main.abra", MockFileProvider::single_file(src)).unwrap_err();
}
