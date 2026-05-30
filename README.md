# The Abra Programming Language

[![Build Status](https://github.com/anandrav/abra/workflows/CI/badge.svg)](https://github.com/anandrav/abra/actions?workflow=CI)

```rust,f#
fn fib(n) {
  if n < 2 {
    return n
  }
  fib(n - 1) + fib(n - 2)
}


println("The first 10 fibonacci numbers are:")
for i in 10 {
  println(fib(i))
}
```

## Installation

### Homebrew (macOS / Linux)

```
brew install anandrav/abra/abra
```

### From source

Requires [Rust and Cargo](https://www.rust-lang.org/tools/install).

```
git clone https://github.com/anandrav/abra.git
cd abra
./scripts/install
```

Optionally install editor extensions:

```
./scripts/install --vim      # Vim syntax highlighting
./scripts/install --vscode   # VS Code extension (requires Node/npm)
./scripts/install --intellij   # VS Code extension (requires Java)
```

## Documentation

User guide and language
reference: [https://anandrav.github.io/abra/about.html](https://anandrav.github.io/abra/about.html)

## License

Abra is distributed under the [Mozilla Public License 2.0](LICENSE.txt).

The MPL is a file-level copyleft license: you can use Abra in your own projects (including proprietary ones), but modifications to Abra's source files must be released under the same license. If you ship Abra as part of a product, include the MPL 2.0 license text and a link to this repository in your third-party notices.
