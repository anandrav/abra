# Foreign Functions

Sometimes you want to do something Abra can't do on its own — talk to the file system, send a network request, or run code that needs to be as fast as possible. Foreign functions let you call Rust from Abra.

The flow looks like this: you write the function signature in Abra, then write the actual implementation as a normal safe Rust function. A build script wires the two together.

## Declaring a foreign function

In an Abra file, mark a function with `#foreign` and leave the body off:

```
// in os.abra
#foreign
fn fread(path: string) -> string

#foreign
fn fwrite(path: string, contents: string) -> void
```

That's all the Abra side looks like. The compiler trusts that an implementation will exist at runtime.

## Project layout

Each top-level namespace that has foreign declarations gets one Rust project, in a `rust_project/` directory next to the Abra modules. So if your top-level namespace is `os`, the layout looks like this:

```
- os.abra
- os/
    - exec.abra
    - rust_project/
        - Cargo.toml
        - build.rs
        - src/
            - lib.rs              (one-liner — see below)
            - os/
                - mod.rs
                - exec.rs         (impl for os/exec.abra)
            - os.rs               (impl for os.abra)
```

The Rust file path mirrors the Abra file path. A foreign function in `os.abra` is implemented in `rust_project/src/os.rs`; one in `os/exec.abra` lives in `rust_project/src/os/exec.rs`.

## Cargo.toml

The Rust project produces a `cdylib` so the Abra runtime can load it dynamically. It depends on `abra_core` both as a regular dependency and as a build dependency:

```toml
[package]
name = "abra_module_os"
version = "0.0.0"
edition = "2024"

[lib]
crate-type = ["cdylib"]

[dependencies]
abra_core = { workspace = true }

[build-dependencies]
abra_core = { workspace = true }
```

## build.rs

The build script reads your `.abra` files, finds the `#foreign` declarations, and generates the unsafe glue code that bridges the VM to your safe Rust functions. You only need one line:

```rust
fn main() {
    abra_core::foreign_bindings::generate_bindings_for_crate();
}
```

## src/lib.rs

`lib.rs` just pulls in the generated glue:

```rust
include!(concat!(env!("OUT_DIR"), "/lib.rs"));
```

You don't edit this file.

## Writing the implementation

Write each foreign function as an ordinary safe Rust function. The name and parameter types match the Abra declaration:

```rust
// in src/os.rs
use std::fs;

pub fn fread(path: String) -> String {
    fs::read_to_string(path).expect("Unable to read file")
}

pub fn fwrite(path: String, contents: String) {
    fs::write(path, contents).expect("Unable to write file");
}
```

### Type mapping

Here's how Abra types correspond to Rust types in your function signatures:

| Abra type             | Rust type                                |
|-----------------------|------------------------------------------|
| `int`                 | `abra_core::vm::AbraInt` (i64)           |
| `float`               | `f64`                                    |
| `bool`                | `bool`                                   |
| `string`              | `String`                                 |
| `void`                | `()`                                     |
| `option<T>`           | `Option<T>`                              |
| `result<T, E>`        | `Result<T, E>`                           |
| `array<T>`            | `Vec<T>`                                 |
| `(T, U)`              | `(T, U)`                                 |
| `#foreign type Foo`   | a generated Rust struct/enum named `Foo` |

### Foreign types

You can also share a custom type between Abra and Rust. Mark a `type` declaration with `#foreign`, and the build script generates a matching Rust enum or struct:

```
#foreign
type FsError =
    | NotFound(string)
    | PermissionDenied(string)
    | Other(string)
```

Import it from the generated module and use it in your function signatures:

```rust
use crate::ffi::core::fs::FsError;

pub fn read(path: String) -> Result<String, FsError> {
    std::fs::read_to_string(&path).map_err(|e| FsError::Other(e.to_string()))
}
```

## Building

Build the native module with cargo:

```
cargo build --package abra_module_os
```

The Abra runtime loads the resulting `cdylib` the first time your program calls one of its foreign functions.

## Host functions

There's a related attribute, `#host`, for functions provided directly by the runtime that's running your Abra program (rather than loaded from a `cdylib`). The prelude uses this for `print_string`, `readline`, and `get_args`. Most users never need to write `#host` functions — they're a hook for programs that embed the Abra VM as a library and want to expose their own callbacks.
