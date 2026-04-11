/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::helper::unwrap_or_panic;
use abra_core::MockFileProvider;
use abra_core::compile_bytecode;

// POSITIVE TESTS
// Name resolution should succeed.

// #[test]
// fn integer_operators() {
//     let src = r#"
// let a = 2 + 2
// let b = a * 3
// let c = b / 2
// let d = c - 1
// let e = d ^ 2
// let f = e % 3
// "#;
//     unwrap_or_panic(compile_bytecode(
//         "main.abra",
//         MockFileProvider::single_file(src),
//     ));
// }

// NEGATIVE TESTS
// Name resolution should catch an error.

// TODO: this is duplicated, move to helper.rs
fn should_fail(src: &str) {
    compile_bytecode("main.abra", MockFileProvider::single_file(src)).unwrap_err();
}

#[test]
fn toplevel_var_referenced_by_func() {
    should_fail(
        r#"
var x = 0

fn hello() {
  println(x)
}

hello()
"#,
    );
}
