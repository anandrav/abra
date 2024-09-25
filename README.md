# The Abra Programming Language

[![Build Status](https://github.com/anandrav/abra/workflows/CI/badge.svg)](https://github.com/anandrav/abra/actions?workflow=CI)

```ocaml
fn fib(n) = {
    match n {
        0 -> 0
        1 -> 1
        _ -> fib(n-1) + fib(n-2)
    }
}

println("The first 10 fibonacci numbers are:")
var i = 0
while i < 10 {
    println(fib(i))
    i <- i + 1
}
```

Try the [online editor](https://abra-editor.replit.app).

## Installation

```
git clone https://github.com/anandrav/abra.git
cd abra
./scripts/install
```