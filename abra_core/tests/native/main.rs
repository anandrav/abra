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

#[test]
fn exit1() {
    let src = r#"
exit(1)
"#;
    expect_exit_code(src, 1);
}

#[test]
fn addition() {
    let src = r#"
exit(2 + 2)
"#;
    expect_exit_code(src, 4);
}
