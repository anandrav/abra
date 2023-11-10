# The Abra Programming Language

[![Build Status](https://github.com/anandrav/abra/workflows/CI/badge.svg)](https://github.com/anandrav/abra/actions?workflow=CI)

```ocaml
func fibonacci(n) = {
    match n
        0 -> 0
        1 -> 1
        _ -> fibonacci(n-1) + fibonacci(n-2)
}

println("The first 10 fibonacci numbers are:")
for_each(range(0, 9), n -> println(fibonacci(n)))
```

Try the [online editor](https://abra-editor.anandrav.repl.co/).

## Running on Desktop

`cargo run`

On Linux you'll need these dependencies:

`sudo apt install gcc cmake libxft-dev`

## Running on Web

[Trunk](https://trunkrs.dev/) is used to build for the web browser. The editor is compiled to [WASM](https://en.wikipedia.org/wiki/WebAssembly).
1. Add WASM target with `rustup target add wasm32-unknown-unknown`
2. Install Trunk with `cargo install trunk`
3. Run `trunk serve` to build and serve on `http://127.0.0.1:8080`
4. Open `http://127.0.0.1:8080/index.html#dev`
