# Patterns

Patterns describe the shape of a value. They appear in:

- `match` expressions
- `let` and `var` bindings (for destructuring)
- `for` loops (for destructuring the loop variable)

### Wildcard

`_` matches anything and binds nothing. Use it as a catch-all or to ignore parts of a value.

```
match n {
    0 -> "zero"
    _ -> "non-zero"
}
```

### Binding

A bare identifier matches anything and binds the value to that name:

```
match get_score() {
    score -> println("got " .. score)
}
```

### Literal

Match against a specific value. Works for `int`, `float`, `string`, `bool`, and `nil`.

```
match command {
    "quit" -> exit_game()
    "help" -> show_help()
    _ -> println("unknown")
}
```

### Variant

Match an enum variant. Use leading-dot syntax. Variants with no data take no parentheses; variants with data destructure their fields:

```
type Shape =
    | Circle(float)
    | Rectangle(float, float)
    | Origin

match shape {
    .Circle(r) -> 3.14 * r * r
    .Rectangle(w, h) -> w * h
    .Origin -> 0.0
}
```

Patterns can be nested. Here we match a list-of-options and pull out the inner value:

```
match maybe_list {
    .some(.cons(head, _)) -> head
    .some(.empty) -> 0
    .none -> -1
}
```

### Tuple

Destructure a tuple by writing a tuple pattern. The pattern can mix wildcards, literals, bindings, and other patterns.

```
match point {
    (0, 0) -> "origin"
    (0, _) -> "on y-axis"
    (_, 0) -> "on x-axis"
    (x, y) -> "(" .. x .. ", " .. y .. ")"
}
```

### Destructuring in `let`

You can destructure tuples directly in a binding:

```
let (x, y) = get_position()
let (name, age) = ("Alice", 30)
```

This is just a special case of pattern matching.

### Match is exhaustive

The compiler checks that match expressions cover every possible value. If you forget a case, you'll get a compile-time error pointing out which patterns are missing. Use `_` as a catch-all when you don't want to enumerate every variant.
