/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

fn run_fs_test(test_name: &str) -> String {
    utils::command!("cargo build --package abra_module_core").unwrap();
    let output = std::process::Command::new("cargo")
        .args([
            "run",
            "--package",
            "abra_cli",
            "--bin",
            "abra",
            "--",
            "--standard-modules",
            "../modules",
            "fs.abra",
            test_name,
        ])
        .output()
        .unwrap();

    let stderr = String::from_utf8(output.stderr).unwrap();
    if !output.status.success() {
        panic!("fs test '{test_name}' failed.\nstderr: {stderr}");
    }
    if !stderr.is_empty() {
        println!("stderr: {stderr}");
    }

    String::from_utf8(output.stdout).unwrap()
}

#[test]
fn fs_read_write() {
    let output = run_fs_test("read_write");
    assert_eq!(output, "hello world\nhello worldline2\n");
}

#[test]
fn fs_exists_copy_rename_remove() {
    let output = run_fs_test("exists_copy_rename_remove");
    assert_eq!(
        output,
        "\
true
false
true
false
true
false
false
"
    );
}

#[test]
fn fs_directories() {
    let output = run_fs_test("directories");
    assert_eq!(
        output,
        "\
true
false
2
false
true
"
    );
}

#[test]
fn fs_path_manipulation() {
    let output = run_fs_test("path_manipulation");
    assert_eq!(
        output,
        "\
foo/bar.txt
some(/a/b)
some(c.txt)
some(txt)
some(c)
none
some()
"
    );
}

#[test]
fn fs_environment() {
    let output = run_fs_test("environment");
    assert_eq!(
        output,
        "\
true
true
true
"
    );
}

#[test]
fn fs_glob_and_walk() {
    let output = run_fs_test("glob_and_walk");
    assert_eq!(
        output,
        "\
2
3
1
4
"
    );
}

#[test]
fn fs_metadata() {
    let output = run_fs_test("metadata");
    assert_eq!(
        output,
        "\
true
false
12
true
"
    );
}

#[test]
fn fs_symlinks() {
    let output = run_fs_test("symlinks");
    assert_eq!(
        output,
        "\
true
false
_test_sym.txt
linked content
"
    );
}

#[test]
fn fs_permissions() {
    let output = run_fs_test("permissions");
    assert_eq!(
        output,
        "\
false
true
false
"
    );
}

#[test]
fn fs_error_handling() {
    let output = run_fs_test("error_handling");
    assert_eq!(
        output,
        "\
caught not found
caught not found
caught not found
not found: No such file or directory (os error 2)
"
    );
}
