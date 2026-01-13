# Installation

To install Abra, download the repository from https://github.com/anandrav/abra.
Then, run the script located at /scripts/install

```
git clone https://github.com/anandrav/abra
cd abra
./scripts/install
```

After, you should be able to run Abra from the command line

```
Usage: abra [OPTIONS] <FILE> [ARGS]...

Arguments:
    <FILE>    The main Abra file to compile and execute
    [ARGS]    Arguments for the Abra program

Options:
    --standard-modules <DIRECTORY>     Override the default standard modules directory
    -a, --assembly                     Print the assembly for the Abra program
    -h, --help                         Print help
```

### Requirements

#### Cargo

Cargo, the Rust package manager, is required to run the install script. The best way to install Cargo is by
using [rustup](https://www.rust-lang.org/tools/install).

#### Node

If you're using Visual Studio Code and want to install the Abra extension, you'll want
to [install Node](https://nodejs.org/en/download/package-manager) as well before running the install script.