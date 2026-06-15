/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use utils::command;

fn build_c_ffi_module() {
    use std::path::PathBuf;
    use std::process::Command;

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let module_dir = manifest_dir.join("modules").join("test_c_ffi");
    let build_dir = module_dir.join("build");
    std::fs::create_dir_all(&build_dir).unwrap();

    let lib_name = format!(
        "{}abra_module_test_c_ffi{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    );
    let output = build_dir.join(lib_name);

    let mut command = Command::new("cc");
    command
        .arg("-shared")
        .arg("-fPIC")
        .arg(module_dir.join("test_c_ffi.c"))
        .arg("-o")
        .arg(output);

    let output = command.output().unwrap();
    if !output.status.success() {
        panic!(
            "failed to build C FFI module\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

fn build_raylib_module() {
    use std::path::PathBuf;
    use std::process::Command;

    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let repo_dir = manifest_dir.parent().unwrap();
    let output = Command::new("make")
        .arg("-C")
        .arg("modules/raylib")
        .current_dir(repo_dir)
        .output()
        .unwrap();
    if !output.status.success() {
        panic!(
            "failed to build Raylib module\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn test_ffi() {
    command!("cargo build --package abra_module_test_ffi").unwrap();
    let output =
        command!("cargo run --package abra_cli --bin abra -- --standard-modules modules ffi.abra")
            .unwrap();

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{stdout_str}");
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(
        stdout_str,
        r#"35
false
nil
mystring
23
true
nil
another
yet another
(true, 2, 3)
some
[ 1, 2, 3, 4, 5, 6 ]
[ [ a, b ], [ c ] ]
42 test
99
true
programs=["echo"] stdin=None
"#
    );
}

#[test]
fn test_c_ffi() {
    build_c_ffi_module();
    let output = command!(
        "cargo run --package abra_cli --bin abra -- --standard-modules modules c_ffi.abra"
    )
    .unwrap();

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{stdout_str}");
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(
        stdout_str,
        r#"42
true
"#
    );
}

#[test]
fn test_ffi_scheduler_continues_during_blocking_call() {
    build_c_ffi_module();
    let output = command!(
        "cargo run --package abra_cli --bin abra -- --standard-modules modules ffi_scheduler.abra"
    )
    .unwrap();

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{stdout_str}");
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(stdout_str, "scheduler alive\n");
}

#[test]
fn test_raylib_module_loads() {
    build_raylib_module();
    let output = command!(
        "cargo run --package abra_cli --bin abra -- --standard-modules ../modules raylib_import.abra"
    )
    .unwrap();

    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{stdout_str}");
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(
        stdout_str,
        r#"256
230
41
55
255
"#
    );
}

#[test]
fn test_host_funcs() {
    let output = command!("cargo run --package test_host_funcs").unwrap();
    let stdout_str = String::from_utf8_lossy(&output.stdout);
    println!("{stdout_str}");
    println!("{}", String::from_utf8(output.stderr).unwrap());
    assert_eq!(output.status.code().unwrap(), 0);
}
