# Operators

### Arithmetic

`+`, `-`, `*`, `/`, `%`, `^` work on `int` and `float`. Both operands must have the same type — Abra does not auto-convert between `int` and `float`.

```
let x = 5 + 2       // 7
let y = 7.5 - 2.5   // 5.0
let r = 13 % 5      // 3 (modulo)
let p = 2 ^ 8       // 256 (power)
```

Unary `-` negates a number:

```
let n = -5
let f = -3.14
```

### String concatenation

The `..` operator concatenates two values into a string. Either operand may be any type that implements the `ToString` interface, so you can mix strings, numbers, and other values without converting them first:

```
let name = "Merlin"
let age = 73
let msg = name .. " is " .. age .. " years old."
// "Merlin is 73 years old."
```

`+` is **not** for string concatenation — that's only for numbers.

### Comparison

`==` and `!=` work on any type that implements `Equal`. `<`, `<=`, `>`, `>=` work on any type that implements `Ord`.

```
let a = 5 == 5      // true
let b = "x" != "y"  // true
let c = 3 < 7       // true
let d = "apple" < "banana"  // true (lexicographic)
```

### Logical

`and`, `or`, `not` are keywords (not `&&`, `||`, `!`):

```
if x > 0 and x < 10 {
    println("in range")
}

if not done {
    keep_going()
}
```

`and` and `or` short-circuit.

### Assignment

Plain assignment uses `=`. Compound assignment operators are also available:

```
var x = 0
x = 10      // simple
x += 5      // x = x + 5
x -= 1      // x = x - 1
x *= 2      // x = x * 2
x /= 4      // x = x / 4
x %= 3      // x = x % 3
```

Only `var` bindings, array elements, and struct fields can be assigned to.

### Indexing

`arr[i]` and `arr[i] = value` index into arrays. The same syntax works on any type that implements the `Index` interface, including `map` and `JsonValue`:

```
let arr = [10, 20, 30]
let first = arr[0]     // 10
arr[1] = 99            // arr = [10, 99, 30]

use core/map
let m: map<string, int> = map.new()
m["alice"] = 100        // calls Index.index_set
let score = m["alice"]  // calls Index.index_get
```

### Unwrap (`!`)

Postfix `!` extracts the value from an `option` or `result`, panicking if it's `none` / `err`. Use it when you know the value is present:

```
let n = "42".to_int()!     // panics if not a valid int
```

### Try (`?`)

Postfix `?` propagates `none`/`err` to the caller. The enclosing function must return a compatible `option` or `result`:

```
use core/fs

fn read_two(a: string, b: string) -> result<string, FsError> {
    let first = read(a)?       // early-return on err
    let second = read(b)?
    .ok(first .. second)
}
```

### Operator precedence

From lowest to highest:

| Precedence | Operators                  | Description           |
|------------|----------------------------|-----------------------|
| 1          | `and`, `or`                | logical               |
| 2          | `==`, `!=`                 | equality              |
| 3          | `..`                       | string format/concat  |
| 5          | `<`, `<=`, `>`, `>=`       | comparison            |
| 6          | `+`, `-` (binary or unary) | additive              |
| 7          | `*`, `/`                   | multiplicative        |
| 8          | `%`                        | modulo                |
| 9          | `^`                        | power                 |
| 10         | `not`                      | prefix                |
| 11         | `.field`                   | member access         |
| 12         | `[index]`                  | index                 |
| 13         | `f(args)`                  | function call         |
| 14         | `!`                        | unwrap                |
| 15         | `?`                        | try                   |
