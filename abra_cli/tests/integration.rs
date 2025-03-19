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
