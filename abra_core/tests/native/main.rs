/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

mod helper;

use crate::helper::expect_exit_code;
use crate::helper::unwrap_or_panic;
use abra_core::MockFileProvider;
use abra_core::compile_bytecode;
use abra_core::vm::Runtime;
use abra_core::vm::{RuntimeStatusKind, VmStatus};
use std::collections::HashMap;
use std::path::PathBuf;

#[test]
fn empty() {
    let src = "";
    expect_exit_code(src, 0);
}

// #[test]
// fn arithmetic() {
//     let src = r#"
// fn sub(x, y) {
//   x - y
// }
// let x = 3
// let y = 4
// let z = sub(x, y)
// let h = sub(z, 1)
// h
// "#;
//     expect_exit_code(src, 0);
// }
