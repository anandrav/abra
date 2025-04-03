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
