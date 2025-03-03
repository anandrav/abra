// tests/cli.rs
use std::process::Command;

#[test]
fn test_cli_output() {
    let output = Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("abra")
        .arg("--") // The '--' tells Cargo that subsequent arguments are for the program, not Cargo
        .arg("tests/hello_world.abra") // Replace with actual CLI arguments
        .output()
        .expect("Failed to execute command");

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert!(output.status.success());
    assert_eq!(stdout_str, "hello world\n");
}

#[test]
fn test_ffi() {
    let output = Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("abra")
        .arg("--") // The '--' tells Cargo that subsequent arguments are for the program, not Cargo
        .arg("--modules")
        .arg("tests/modules")
        .arg("--shared-objects")
        .arg("../target/debug")
        .arg("tests/ffi.abra") // Replace with actual CLI arguments
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
"#
    );
}
