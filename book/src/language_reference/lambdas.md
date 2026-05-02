# Lambdas

A lambda is an anonymous function written inline. Use lambdas to pass behavior as a value: as an argument to another function, or stored in a variable.

### Single argument

When a lambda has exactly one parameter, parentheses are optional:

```
let double = x -> x * 2
let n = double(5)   // 10
```

### Multiple arguments

Wrap the parameter list in parentheses:

```
let add = (a, b) -> a + b
let s = add(3, 4)   // 7
```

### Type annotations

Parameter and return types can be annotated, but are usually inferred:

```
let add = (a: int, b: int) -> a + b
```

### Block body

A lambda body can be a block instead of a single expression. The last expression in the block is the return value:

```
let greet = (name: string) -> {
    let msg = "Hello, " .. name
    println(msg)
    msg
}
```

### Lambdas as arguments

Many standard library functions take lambdas. For example, `sort_by` takes a comparator:

```
let arr = [3, 1, 4, 1, 5, 9]
arr.sort_by((a, b) -> a <= b)
```

### Capturing values

A lambda captures the values of variables in its enclosing scope by value at the time the lambda is created. Captured values can be read inside the lambda body but cannot be reassigned.

```
let multiplier = 10
let scale = x -> x * multiplier
let n = scale(5)   // 50
```

### Lambda types

A lambda's type is written `(ArgType, ...) -> ReturnType`:

```
let f: (int, int) -> int = (a, b) -> a + b
let p: (string) -> bool = s -> s.starts_with("yes")
```
