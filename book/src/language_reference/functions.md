# Functions

A function is a reusable piece of code that takes zero or more inputs and has a single output.

```
fn distance(x1, y1, x2, y2) {
    sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
}
```

Functions can be recursive.

```
fn fibonacci(n: int) -> int {
    if n < 2 {
        n
    } else {
        fibonacci(n-2) + fibonacci(n-1) // recursive calls to fibonacci()
    }
}
```

The last expression in the body of the function is the return value. You can also return early from a function.
If a function's body doesn't have a last expression, the function returns `void`, which means it returns `nil` which is nothing.

```
fn fibonacci(n: int) -> int {
    if n <= 1 {
        return n            // early return
    }
    fib(n-2) + fib(n-1)     // last expression is return value
}

fn display_message() -> void {
    for n in 5 {            // last statement is a for loop. No return value
        println(n)
    }
}
```

For convenience, if a function body is just a single expression, the body can be written after an equal sign `=` instead
of
being wrapped in a curly brace block:

```
fn distance(x1, y1, x2, y2) = sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
```

### Default arguments

A parameter can be given a default value with `=`. Callers can omit any trailing argument that has a default.

```
fn greet(name: string, greeting: string = "Hello") {
    println(greeting .. ", " .. name)
}

greet("Alice")              // "Hello, Alice"
greet("Bob", "Howdy")       // "Howdy, Bob"
```

### Named arguments

At a call site, you can pass an argument by name with `=`. This is useful when a function takes several parameters with defaults and you want to override one in the middle.

```
fn greet(name: string, greeting: string = "Hello", excited: bool = false) {
    let punct = if excited { "!" } else { "." }
    println(greeting .. ", " .. name .. punct)
}

greet("Carol", excited = true)              // "Hello, Carol!"
greet("Dave", greeting = "Hi", excited = true)
```

Named arguments must come after all positional arguments at the call site.