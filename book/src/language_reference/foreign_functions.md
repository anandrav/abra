# Foreign Functions

Functions implemented in Rust can be called from Abra. These are called *foreign functions*. Use them to expose system capabilities (file I/O, networking, hardware access) or performance-critical code that you'd rather write in Rust.

## Declaring a foreign function

In an Abra file, declare a foreign function using the `#foreign` attribute. The declaration has no body — the implementation lives in Rust.

```
// in os.abra
#foreign
fn fread(path: string) -> string

#foreign
fn fwrite(path: string, contents: string) -> void
```

The Abra type signature determines the Rust signature of the corresponding implementation.

## Project layout

For each top-level namespace that has any foreign declarations, there must be a single Rust project beside the Abra modules. The project lives in a directory called `rust_project/` inside the namespace.

For example, if your top-level namespace is `os`, the layout is:

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

A foreign function declared in `os.abra` is implemented in `rust_project/src/os.rs`. A foreign function declared in `os/exec.abra` is implemented in `rust_project/src/os/exec.rs`. The Rust file path mirrors the Abra file path.

## Cargo.toml

The Rust project must be a `cdylib` so it can be loaded at runtime via `dlopen`. It depends on `abra_core` both as a normal dependency and as a build dependency.

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

The build script calls into `abra_core` to generate the FFI glue (the unsafe code that pops arguments off the VM stack, calls your safe Rust function, and pushes the result back).

```rust
fn main() {
    abra_core::foreign_bindings::generate_bindings_for_crate();
}
```

This reads every `.abra` file alongside the Rust project, finds the `#foreign` declarations, and emits a `lib.rs` into the build's `OUT_DIR`.

## src/lib.rs

`lib.rs` is just one line — it pulls in the generated glue:

```rust
include!(concat!(env!("OUT_DIR"), "/lib.rs"));
```

You should not edit this file.

## Writing the implementations

Implement each foreign function as an ordinary safe Rust function. The function name and parameter types must match the Abra declaration.

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

You can also declare foreign types — Abra types whose representation is generated to match a Rust type. Use `#foreign` on a `type` declaration:

```
#foreign
type FsError =
    | NotFound(string)
    | PermissionDenied(string)
    | Other(string)
```

The build script generates a matching Rust enum. You import it from the generated module and return it from your safe Rust functions:

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

The resulting `cdylib` is loaded at runtime when the Abra program first calls one of its foreign functions.

## Host functions

A related attribute, `#host`, marks a function as one that the embedding runtime provides directly (rather than being loaded from a `cdylib`). The prelude uses this for `print_string`, `readline`, and `get_args`. Most users don't write `#host` functions — they're a hook for programs that embed the Abra VM as a library and need to expose custom callbacks.
