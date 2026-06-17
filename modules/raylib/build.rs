use std::process::Command;

fn main() {
    let manifest_dir = std::path::PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let modules_dir = manifest_dir.parent().unwrap().to_path_buf();
    let generated_dir = manifest_dir.join("build").join("generated");
    let output = manifest_dir.join("build").join(format!(
        "{}abra_module_raylib{}",
        std::env::consts::DLL_PREFIX,
        std::env::consts::DLL_SUFFIX
    ));

    println!("cargo:rerun-if-changed=../raylib.abra");
    println!("cargo:rerun-if-changed=raylib.c");
    println!("cargo:rerun-if-env-changed=CC");

    abra_core::foreign_bindings::generate_c_bindings(
        &abra_core::foreign_bindings::CBindingsConfig {
            module: "raylib".to_string(),
            root: modules_dir,
            out_dir: generated_dir.clone(),
        },
    )
    .expect("failed to generate C bindings for the Raylib Abra module");

    std::fs::create_dir_all(output.parent().unwrap()).unwrap();

    let compiler = std::env::var("CC").unwrap_or_else(|_| "cc".to_string());
    let mut command = Command::new(compiler);
    command
        .current_dir(&manifest_dir)
        .arg("-O2")
        .arg("-Wall")
        .arg("-Wextra")
        .arg("-std=c11");

    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap();
    if target_os == "windows" {
        command.arg("-shared");
    } else if target_os == "macos" {
        command.arg("-fPIC").arg("-dynamiclib");
    } else {
        command.arg("-fPIC").arg("-shared");
    }

    command
        .arg("raylib.c")
        .arg(generated_dir.join("abra_raylib_glue.c"))
        .arg("-o")
        .arg(&output);

    if target_os != "windows" && target_os != "macos" {
        command.arg("-ldl");
    }

    let output = command
        .output()
        .expect("failed to run C compiler for the Raylib Abra module");

    if !output.status.success() {
        panic!(
            "failed to build the Raylib Abra module\nstdout:\n{}\nstderr:\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
}
