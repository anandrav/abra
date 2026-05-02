# Variables

A variable holds a value. Use `let` for a constant, and `var` for a mutable variable.

```
let x = 5
let pi = 3.14159
let name = "Merlin"
```

A `var` can be reassigned with `=`:

```
var score = 0
score = 10
score = score + 5    // 15
```

Trying to reassign a `let` is a compile error — that's the point. Reach for `var` only when you actually need mutation.

### Type annotations

Most of the time you don't need to annotate the type — Abra figures it out from the value you assign:

```
let x = 5         // x is int
let pi = 3.14     // pi is float
let yes = true    // yes is bool
```

When you do want to be explicit (or when the compiler can't tell), put the type after a colon:

```
let x: int = 2
let pi: float = 3.14
let p: (int, int) = (1, 2)
```
