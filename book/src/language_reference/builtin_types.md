# Built-in Types

Abra has a small set of built-in types. Most programs are written using these plus your own structs and enums.

### int

A 64-bit signed integer. The usual arithmetic operators all work on it.

```
let a = 5
let b = 2 + 3       // 5
let c = 2 * 3       // 6
let d = 12 / 3      // 4
let e = 13 / 3      // also 4 — integer division truncates
let f = 2 ^ 8       // 256 (power)
let g = 13 % 5      // 3 (modulo)
```

### float

A 64-bit floating-point number. The same arithmetic operators apply, but you can't mix `int` and `float` directly — convert with `int_to_float` or `float_to_int`.

```
let pi = 3.14159
let area = pi * 2.0 * 2.0
let n = float_to_int(pi)    // 3
```

### bool

```
let shield_is_equipped = true
let sword_is_equipped = false
```

Combine with `and`, `or`, and `not` (see [Operators](./operators.md)).

### string

A garbage-collected, immutable Unicode string. Use the `..` operator to build new strings out of existing values:

```
let name = "Merlin"
let age = 73
let message = name .. " is " .. age .. " years old."
// "Merlin is 73 years old."
```

For slicing, splitting, searching, and parsing, see the [`core/strings`](./standard_library.md#corestrings) module.

### array&lt;T&gt;

A growable list of elements that all have the same type. Indexing is zero-based.

```
let arr = [1, 2, 3, 4]
arr.push(5)        // [1, 2, 3, 4, 5]
arr.len()          // 5
arr[2]             // 3
arr[2] = 49        // [1, 2, 49, 4, 5]
arr.pop()          // [1, 2, 49, 4]
```

You can't mix types in one array — `[1, 2.0]` is an error. Use a tuple if you need different types together.

### tuples

A tuple groups a fixed number of values, possibly of different types:

```
let pair = (1, 2)
let coordinate = (1.0, 2.0, -3.0)
let person = ("Lancelot", 19)
```

Tuples are useful when you want to return a couple of related things from a function, or store a few related values together without inventing a struct.

You can pull a tuple apart with destructuring (see [Patterns](./patterns.md)):

```
let (name, age) = person
```

The prelude provides equality, comparison, hashing, and `ToString` for tuples up to size 4.

### void

Represents nothing. Its only value is `nil`. Functions that don't return anything meaningful return `void`:

```
fn greet(name: string) {
    println("Hello, " .. name)
    // implicitly returns nil
}

fn maybe_greet(name: string, should_greet: bool) {
    if not should_greet {
        return nil      // explicit early return
    }
    println("Hello, " .. name)
}
```

### never

A type with zero values. It's the return type of functions that don't return at all — for example, `panic()` aborts the program, so its return type is `never`.
