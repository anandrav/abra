# Installation

To install Abra, clone the repository and run the install script.

```
git clone https://github.com/anandrav/abra
cd abra
./scripts/install
```

This builds the Abra CLI in release mode and installs it via `cargo install` along with the LSP server. It also copies the standard library modules into `~/.abra/abra/`.

### Install script options

The install script accepts a few flags:

| Flag           | Effect                                                   |
|----------------|----------------------------------------------------------|
| `--quick`      | Use a debug build instead of release (faster to install) |
| `--vim`        | Install Vim syntax highlighting and ftdetect             |
| `--vscode`     | Build and install the VS Code extension (requires Node)  |
| `--intellij`   | Build and install the IntelliJ plugin (requires JDK 21)  |

Example:

```
./scripts/install --vim --vscode
```

### Using the CLI

After installing, the `abra` command is available on your PATH:

```
Usage: abra [OPTIONS] <FILE> [ARGS]...

Arguments:
    <FILE>    The main Abra file to compile and execute
    [ARGS]    Arguments for the Abra program

Options:
    -h, --help                           Print help
    -c, --check                          Check for errors without compiling and running
    -i, --import-dir <DIRECTORY>         Provide an additional import directory

Additional options:
    --standard-modules <DIRECTORY>       Override the default standard modules directory
    -a, --assembly                       Print the assembly for the Abra program
    --debug-log                          Enable internal debug logging (debug builds only)
```

By default, `abra` searches for imported modules in:
1. The directory containing the main file
2. Any directory passed with `-i` / `--import-dir`
3. The standard modules directory (`~/.abra/abra/modules` by default; override with `--standard-modules`)

## Requirements

### Cargo

Cargo, the Rust package manager, is required to run the install script. The recommended way to get Cargo is via [rustup](https://www.rust-lang.org/tools/install).

### Node (optional)

If you plan to install the VS Code extension with `--vscode`, you'll need [Node.js](https://nodejs.org/en/download/package-manager) (which provides `npm`).

### JDK 21 (optional)

If you plan to install the IntelliJ plugin with `--intellij`, you'll need JDK 21. On macOS:

```
brew install openjdk@21
```
