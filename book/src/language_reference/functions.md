# Functions

A function packages up a piece of work so you can call it by name. Declare one with `fn`:

```
fn distance(x1, y1, x2, y2) {
    sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
}
```

Calls look like in most languages:

```
let d = distance(0.0, 0.0, 3.0, 4.0)   // 5.0
```

### Parameter and return types

Parameter types are usually inferred. You can annotate them when you want to be explicit, and add a return type with `->`:

```
fn double(x: int) -> int {
    x * 2
}
```

### Recursion

Functions can call themselves:

```
fn fibonacci(n: int) -> int {
    if n < 2 {
        n
    } else {
        fibonacci(n - 2) + fibonacci(n - 1)
    }
}
```

### Returning values

The last expression in the body is the return value — no `return` keyword needed:

```
fn double(x: int) -> int {
    x * 2
}
```

Use `return` for an early exit:

```
fn fibonacci(n: int) -> int {
    if n <= 1 {
        return n
    }
    fibonacci(n - 2) + fibonacci(n - 1)
}
```

A function with no final expression returns `void` (which is `nil`):

```
fn display_message() {
    for n in 5 {
        println(n)
    }
    // implicitly returns nil
}
```

### Expression-bodied functions

When the whole function is a single expression, write it after `=` instead of in a block:

```
fn square(x: int) -> int = x * x

fn distance(x1, y1, x2, y2) = sqrt((x2 - x1) ^ 2 + (y2 - y1) ^ 2)
```

### Default arguments

A parameter can have a default value. Callers can leave any trailing argument off:

```
fn greet(name: string, greeting: string = "Hello") {
    println(greeting .. ", " .. name)
}

greet("Alice")              // "Hello, Alice"
greet("Bob", "Howdy")       // "Howdy, Bob"
```

### Named arguments

You can pass an argument by its parameter name. This lets you skip past parameters that have defaults:

```
fn greet(name: string, greeting: string = "Hello", excited: bool = false) {
    let punct = if excited { "!" } else { "." }
    println(greeting .. ", " .. name .. punct)
}

greet("Carol", excited = true)                  // "Hello, Carol!"
greet("Dave", greeting = "Hi", excited = true)
```

Named arguments must come after all positional arguments.
