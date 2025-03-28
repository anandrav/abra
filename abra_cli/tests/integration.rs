/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// tests/cli.rs
use std::process::Command;

#[test]
fn test_cli_output() {
    let output = Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("abra")
        .arg("--")
        .arg("tests/hello_world.abra")
        .output()
        .expect("Failed to execute command");

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert!(output.status.success());
    assert_eq!(stdout_str, "hello world\n");
}

// TODO: move this test to abra_core/ crate. Shouldn't be much more work than drag-and-drop
#[test]
fn test_ffi() {
    Command::new("cargo")
        .arg("build")
        .arg("--package")
        .arg("test_ffi")
        .output()
        .expect("Failed to execute command");

    let output = Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("abra")
        .arg("--")
        .arg("--modules")
        .arg("tests/modules")
        .arg("--shared-objects")
        .arg("../target/debug")
        .arg("tests/ffi.abra")
        .output()
        .expect("Failed to execute command");

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert!(output.status.success());
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

// TODO: move this test to abra_core/ crate. Shouldn't be much more work than drag-and-drop
#[test]
fn test_host_funcs() {
    Command::new("cargo")
        .arg("build")
        .arg("--package")
        .arg("test_host_funcs")
        .output()
        .expect("Failed to execute command");
    let output = Command::new("cargo")
        .arg("run")
        .arg("--package")
        .arg("test_host_funcs")
        .output()
        .expect("Failed to execute command");
    assert_eq!(output.status.code().unwrap(), 0);
}
