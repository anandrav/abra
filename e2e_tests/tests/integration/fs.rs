/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

fn run_fs_test(test_name: &str) {
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

    if !output.status.success() {
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        panic!("fs test '{test_name}' failed.\nstdout: {stdout}\nstderr: {stderr}");
    }
}

#[test]
fn fs_read_write() {
    run_fs_test("read_write");
}

#[test]
fn fs_exists_copy_rename_remove() {
    run_fs_test("exists_copy_rename_remove");
}

#[test]
fn fs_directories() {
    run_fs_test("directories");
}

#[test]
fn fs_path_manipulation() {
    run_fs_test("path_manipulation");
}

#[test]
fn fs_environment() {
    run_fs_test("environment");
}

#[test]
fn fs_glob_and_walk() {
    run_fs_test("glob_and_walk");
}

#[test]
fn fs_metadata() {
    run_fs_test("metadata");
}

#[test]
fn fs_symlinks() {
    run_fs_test("symlinks");
}

#[test]
fn fs_permissions() {
    run_fs_test("permissions");
}

#[test]
fn fs_error_handling() {
    run_fs_test("error_handling");
}
