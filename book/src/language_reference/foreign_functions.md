# Foreign Functions

Functions implemented in Rust can be called from Abra.
Foreign functions must be declared ahead of time in an Abra file, so that the compiler knows they exist.
The compiler will search for a directory with the same name as the Abra file which contains a Rust project.
That Rust project should use crate-type "cdylib" so that it can be loaded at runtime. It must take `abra_core` as a
dependency. It is recommended to take `abra_core` as a build-dependency as well and to invoke
`generate_bindings_for_crate()` in the project's `build.rs`. This will automatically generate the necessary unsafe glue
code that corresponds with the foreign function declarations. Then, you can implement those foreign functions using safe
Rust.

In order to avoid creating a Rust project (and therefore a cdylib) for every Abra file with a foreign function
declaration, there should be a
single Rust project for every toplevel namespace that contains foreign function declarations.
For example, implementing a foreign function in `os.abra` (os is under the root namespace) should be done in
`os/rust_project/src/os.rs`.
Implementing a foreign function in `os/exec.abra`, which is under the os/ namespace, should be done in
`os/rust_project/src/os/exec.abra` -- the same Rust project.

os.abra

```
foreign fn fread(path: string) -> string

foreign fn fwrite(path: string, contents: string) -> string
```

os/rust_project/Cargo.toml

```
[package]
name = "abra_module_os"

[lib]
crate-type = ["cdylib"]
[dependencies]
abra_core = { workspace = true }

[build-dependencies]
abra_core = { workspace = true }
```

os/rust_project/build.rs

```
fn main() {
    abra_core::addons::generate_bindings_for_crate();
}
```

os/rust_project/src/lib.rs (automatically generated)

```
use abra_core::vm::Vm;
use std::fs;

#[no_mangle]
pub unsafe extern "C" fn fread(vm: *mut Vm) {
    let string_view = vm_view_string(vm);
    let path = string_view.to_owned();
    vm_pop(vm);

    let content = fs::read_to_string(path).expect("Unable to read from file");

    let string_view = StringView::from_string(&content);
    vm_push_string(vm, string_view);
}

#[no_mangle]
pub unsafe extern "C" fn fwrite(vm: *mut Vm) {
    let string_view = vm_view_string(vm);
    let content = string_view.to_owned();
    vm_pop(vm);

    // TODO: make a macro for this called get_string!
    let string_view = vm_view_string(vm);
    let path = string_view.to_owned();
    vm_pop(vm);

    fs::write(path, content).expect("Unable to write to file");
}
```

os/rust_project/src/os.rs

```
use std::fs::self;
use std::io::Write;

pub fn fread(path: String) -> Result<String, String> {
    fs::read_to_string(path).map_err(|e| e.to_string())
}

pub fn fwrite(path: String, content: String) {
    fs::write(path, content).expect("Unable to write to file");
}
```