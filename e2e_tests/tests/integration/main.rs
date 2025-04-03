/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use utils::command;

#[test]
fn test_ffi() {
    command!("cargo build --package abra_module_test_ffi").unwrap();
    let output = command!("cargo run --package abra_cli --bin abra -- --modules modules --shared-objects ../target/debug ffi.abra").unwrap();

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(
        stdout_str,
        r#"35
false
()
mystring
23
true
()
another
yet another
(true, 2, 3)
yes
[ 1, 2, 3, 4, 5, 6 ]
"#
    );
}

#[test]
fn test_host_funcs() {
    let output = command!("cargo run --package test_host_funcs").unwrap();
    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(output.status.code().unwrap(), 0);
}
