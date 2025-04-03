/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::process::Command;

#[test]
fn test_ffi() {
    // TODO: this is such a tiresome way to run commands. Make a wrapper
    // maybe make a macro so you can write command!("cargo build --package abra_module_test_ffi").unwrap()

    // TODO: is this rebuilding actually necessary? shouldn't workspace take care of it? Try adding a dev-dependency on abra_module_test_ffi and test_host_funcs
    Command::new("cargo")
        .arg("build")
        .arg("--package")
        .arg("abra_module_test_ffi")
        .output()
        .expect("Failed to execute command");

    let output = Command::new("cargo")
        .arg("run")
        .arg("--package")
        .arg("abra_cli")
        .arg("--bin")
        .arg("abra")
        .arg("--")
        .arg("--modules")
        .arg("modules")
        .arg("--shared-objects")
        .arg("../target/debug")
        .arg("ffi.abra")
        .output()
        .expect("Failed to execute command");

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
    let output = Command::new("cargo")
        .arg("run")
        .arg("--package")
        .arg("test_host_funcs")
        .output()
        .expect("Failed to execute command");
    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(output.status.code().unwrap(), 0);
}
