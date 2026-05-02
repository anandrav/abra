# Installation

To install Abra, clone the repository and run the install script.

```
git clone https://github.com/anandrav/abra
cd abra
./scripts/install
```

This installs the Abra CLI, the LSP, and the standard library (under `~/.abra/`).

### Editor support

The install script can also set up syntax highlighting and language support for your editor:

| Flag           | Effect                                                  |
|----------------|---------------------------------------------------------|
| `--vim`        | Install Vim syntax highlighting and ftdetect            |
| `--vscode`     | Build and install the VS Code extension (requires Node) |
| `--intellij`   | Build and install the IntelliJ plugin (requires JDK 21) |

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
