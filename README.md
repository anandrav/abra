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
```

## Documentation

User guide and language
reference: [https://anandrav.github.io/abra/about.html](https://anandrav.github.io/abra/about.html)
