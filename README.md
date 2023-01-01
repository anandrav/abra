# The Abra Programming Language

This is the main source code repository for Abra. It contains a GUI editor and the interpreter.
## Running on Desktop

Make sure you are using the latest version of stable rust by running `rustup update`.

`cargo run`

On Linux you need to first run:

`sudo apt-get install libxcb-render0-dev libxcb-shape0-dev libxcb-xfixes0-dev libspeechd-dev libxkbcommon-dev libssl-dev`

## Running on Web

[Trunk](https://trunkrs.dev/) is used to build for web target. The editor is compiled to [WASM](https://en.wikipedia.org/wiki/WebAssembly).
1. Install Trunk with `cargo install --locked trunk`.
2. Run `trunk serve` to build and serve on `http://127.0.0.1:8080`. Trunk will rebuild automatically if you edit the project.
3. Open `http://127.0.0.1:8080/index.html#dev` in a browser. See the warning below.