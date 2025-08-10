# Variables

Variables can be created using the `let` keyword.

```
let x = 5
let y = 8
```

Mutable variables can be created using the `var` keyword.
Their value can be updated using the assignment `:=` operator.

```
var x = 5       // x = 5
x := 6          // x = 6
let y = x + x   // y = 12
```

Variables can be given type annotations. For convenience, they are often not required.

In some situations, type annotations are required, for instance when writing code with generic types, invoking member
functions, or accessing struct fields. They also help the compiler give more tailored error messages in case you make a
mistake.

```
let x: int = 2
let y: float = 3.14
let p: (int, int) = (1, 2)
```