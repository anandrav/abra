/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

// tests/cli.rs
use utils::command;

fn assert_success(output: &std::process::Output) {
    assert!(
        output.status.success(),
        "stdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}

#[test]
fn test_cli_output() {
    let output = command!("cargo run --bin abra -- tests/hello_world.abra").unwrap();

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{stdout_str}");
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert!(output.status.success());
    assert_eq!(stdout_str, "hello world\n");
}

#[test]
fn test_native_compilation() {
    let temp_dir = std::env::temp_dir().join(format!("abra-native-test-{}", std::process::id()));
    std::fs::create_dir(&temp_dir).unwrap();
    let executable = temp_dir.join(format!("program{}", std::env::consts::EXE_SUFFIX));
    let source = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("native.abra");

    let output = std::process::Command::new(env!("CARGO_BIN_EXE_abra"))
        .arg("--native")
        .arg("--output")
        .arg(&executable)
        .arg(source)
        .output()
        .unwrap();
    assert_success(&output);
    assert!(executable.is_file());

    let output = std::process::Command::new(&executable).output().unwrap();
    assert_success(&output);

    std::fs::remove_dir_all(temp_dir).unwrap();
}
