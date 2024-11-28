# The Abra Programming Language

[![Build Status](https://github.com/anandrav/abra/workflows/CI/badge.svg)](https://github.com/anandrav/abra/actions?workflow=CI)

```rust,f#
fn fib(n) = match n {
     0 -> 0
     1 -> 1
     _ -> fib(n-1) + fib(n-2)
}


println("The first 10 fibonacci numbers are:")
var i = 0
while i < 10 {
    println(fib(i))
    i <- i + 1
}
```

## Installation
(Requires Rust and Cargo: https://www.rust-lang.org/tools/install)
(Requires Node to install VS Code extension)
```
git clone https://github.com/anandrav/abra.git
cd abra
./scripts/install
```
