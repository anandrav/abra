# Functions

A function is a piece of code that takes zero or more inputs and has a single output.

```
fn distance(x1: float, x2: float, x2: float, y2: float) -> float {
    sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
}
```

Functions can be recursive.

```
fn fibonacci(n: int) -> int {
    if n <= 1 {
        n
    } else {
        fib(n-2) + fib(n-1)
    }
}
```

The last expression in the body of the function is the return value. You can also return early from a function.

```
fn fibonacci(n: int) -> int {
    if n <= 1 {
        return n        // early return
    }
    fib(n-2) + fib(n-1) // last expression is return value
}
```

A function always returns the value of its body.
If the body of a function is a block of statements, then the last expression of the block is the return value of the
function.