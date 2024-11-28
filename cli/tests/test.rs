// tests/cli.rs
use std::process::Command;

#[test]
fn test_cli_output() {
    let output = Command::new("cargo")
        .arg("run")
        .arg("--bin")
        .arg("abra")
        .arg("--") // The '--' tells Cargo that subsequent arguments are for the program, not Cargo
        .arg("tests/test.abra") // Replace with actual CLI arguments
        .output()
        .expect("Failed to execute command");

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{}", stdout_str);
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert!(output.status.success());
    assert_eq!(stdout_str, "hello from test.abra\n");
}
