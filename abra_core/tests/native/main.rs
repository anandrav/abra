/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

mod helper;

use crate::helper::unwrap_or_panic;
use crate::helper::{expect_value, should_fail};
use abra_core::MockFileProvider;
use abra_core::compile_bytecode;
use abra_core::vm::Runtime;
use abra_core::vm::{RuntimeStatusKind, VmStatus};
use std::collections::HashMap;
use std::path::PathBuf;

#[test]
fn arithmetic() {
    let src = r#"
fn sub(x, y) {
  x - y
}
let x = 3
let y = 4
let z = sub(x, y)
let h = sub(z, 1)
h
"#;
    expect_value(src, -2);
}
