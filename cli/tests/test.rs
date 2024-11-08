// tests/cli.rs
use std::process::Command;

#[test]
fn test_cli_output() {
    let output = Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("abra")
        .arg("--")  // The '--' tells Cargo that subsequent arguments are for the program, not Cargo
        .arg("tests/test.abra") // Replace with actual CLI arguments
        .output()
        .expect("Failed to execute command");

    assert!(output.status.success());
    println!("the output was {:?}", output.stdout);
    assert_eq!(String::from_utf8_lossy(&output.stdout), "hello world\n");
}
