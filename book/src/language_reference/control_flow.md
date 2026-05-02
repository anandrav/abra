# Control Flow

### If-else

`if` runs one block when a condition is true, optionally another when it's false:

```
let is_arriving = true

if is_arriving {
    println("hello")
} else {
    println("good bye")
}
```

Chain conditions with `else if`:

```
let hour = 14

if hour < 12 {
    println("good morning")
} else if hour < 17 {
    println("good afternoon")
} else {
    println("good night")
}
```

`if` is an expression — it returns a value, so you can use it on the right side of a `let`:

```
let label = if temperature > 30 { "hot" } else { "cool" }
```

### Match

`match` checks a value against a series of patterns and runs the first one that fits. It's like a more powerful `if`/`else if` chain.

```
let n = 2
let s = match n {
    0 -> "zero"
    1 -> "one"
    2 -> "two"
    3 -> "three"
    _ -> "something else"
}
// s = "two"
```

The `_` is a catch-all. `match` does much more than literal lookup — it can pull values out of enums and tuples in one step. See [Patterns](./patterns.md) for the full picture.

### While loops

Repeat as long as a condition holds:

```
var n = 3
while n > 0 {
    print("hello")
    n = n - 1
}
// hellohellohello
```

Use `break` to exit a loop early, and `continue` to skip to the next iteration:

```
var i = 0
while true {
    if i >= 5 { break }
    if i % 2 == 0 {
        i += 1
        continue
    }
    println(i)
    i += 1
}
// 1
// 3
```

### For loops

Iterate over anything that can be iterated. Most commonly, that's an array or a count:

```
let arr = [1, 2, 3, 4, 5]
var sum = 0
for n in arr {
    sum = sum + n
}
println(sum)    // 15
```

Iterating over an integer counts from `0` up to (but not including) that integer:

```
for i in 5 {
    println(i)   // prints 0, 1, 2, 3, 4
}
```

For an arbitrary range, use `range(begin, end)`:

```
for i in range(2, 6) {
    println(i)   // prints 2, 3, 4, 5
}
```

`for` works on any type that implements `Iterable` (see [Interfaces](./interfaces.md)), so you can write your own.
