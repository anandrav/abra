# Patterns

A pattern is a way to look at a piece of data and ask "is it shaped like this — and if so, can you pull these parts out for me?" Patterns let you match against a value and unpack it at the same time, in a single step.

You've already seen patterns if you've used a `match` expression. Here's a small one:

```
match command {
    "quit" -> exit_game()
    "help" -> show_help()
    _ -> println("unknown command")
}
```

Each line on the left side of `->` is a pattern. The first pattern that matches `command` wins, and its right side runs.

## Where patterns appear

Three places in Abra accept patterns:

1. **`match` expressions** — choose a branch based on the shape of a value.
2. **`let` and `var` bindings** — pull values apart while binding them to names.
3. **`for` loops** — pull apart each item as you iterate.

## The kinds of patterns

### Match a specific value

A literal pattern matches one specific value. Useful for small lookups:

```
fn day_name(day: int) -> string {
    match day {
        1 -> "Monday"
        2 -> "Tuesday"
        3 -> "Wednesday"
        4 -> "Thursday"
        5 -> "Friday"
        _ -> "weekend"
    }
}
```

Literals can be `int`, `float`, `string`, `bool`, or `nil`.

### Catch everything else

The wildcard `_` matches any value but doesn't bind it to a name. It's how you write "anything else":

```
match user_input {
    "yes" -> proceed()
    "no" -> stop()
    _ -> println("please answer yes or no")
}
```

### Bind a value to a name

A bare identifier matches anything and binds the value to that name. Use it when you want to do something with the value, not just check what it is:

```
match get_age() {
    0 -> println("just born!")
    age -> println("age is " .. age)
}
```

In the second arm, `age` is a fresh variable that holds whatever `get_age()` returned.

### Pull data out of an enum

If a value is an enum variant, you can match the variant and bind the data it carries in one step. Use leading-dot syntax to name the variant:

```
type Shape =
    | Circle(float)
    | Rectangle(float, float)
    | Origin

fn area(s: Shape) -> float {
    match s {
        .Circle(r) -> 3.14 * r * r
        .Rectangle(w, h) -> w * h
        .Origin -> 0.0
    }
}
```

`.Circle(r)` says "if `s` is a `Circle`, run this branch — and let me call its inner float `r`".

If a variant's fields are named, the pattern can name them too, just like [struct patterns](#pull-structs-apart) — use the names for all of the fields or none of them:

```
type Color =
    | Rgb(red: int, green: int, blue: int)
    | Named(string)

match c {
    .Rgb(red = r, green = g, blue = b) -> "rgb(" .. r .. "," .. g .. "," .. b .. ")"
    .Named(name) -> name
}
```

This is the most common use of patterns. It's how you handle `option` and `result`:

```
match read("config.txt") {
    .ok(text) -> println(text)
    .err(e) -> println("oops: " .. e)
}

match user.try_get("nickname") {
    .some(name) -> println("hi, " .. name)
    .none -> println("hi, anonymous")
}
```

### Pull tuples apart

Tuple patterns destructure tuples by writing one. You can mix wildcards, literals, and bindings:

```
match point {
    (0, 0) -> "at the origin"
    (0, y) -> "on the y-axis at height " .. y
    (x, 0) -> "on the x-axis at position " .. x
    (x, y) -> "somewhere at (" .. x .. ", " .. y .. ")"
}
```

Tuple destructuring is the most common form of pattern in `let`:

```
let (x, y) = get_position()
let (name, age) = ("Alice", 30)

let pairs = [(1, "one"), (2, "two"), (3, "three")]
for pair in pairs {
    let (number, word) = pair
    println(number .. " = " .. word)
}
```

### Pull structs apart

Struct patterns destructure a struct by matching each of its fields. Naming the fields makes each arm explicit:

```
type Point = {
    x: int
    y: int
}

match point {
    Point(x = 0, y = 0) -> "at the origin"
    Point(x = 0, y = y) -> "on the y-axis at height " .. y
    Point(x = x, y = 0) -> "on the x-axis at position " .. x
    Point(x = x, y = y) -> "somewhere at (" .. x .. ", " .. y .. ")"
}
```

Fields can also be matched positionally, in declaration order, which is convenient for small structs:

```
match point {
    Point(0, 0) -> "at the origin"
    Point(x, y) -> "somewhere at (" .. x .. ", " .. y .. ")"
}
```

Either way, every field must be matched — use `_` when you don't care about a field's value. Use the names for all of the fields or none of them; mixing the two in one pattern is an error. Named fields may be listed in any order, and are the safer choice for structs with many fields: if you reorder a struct's fields, patterns that name them keep working instead of silently binding the wrong values.

```
match person {
    Person(name = "Alice", age = _) -> "hi, Alice!"
    Person(name = n, age = _) -> "hello, " .. n
}
```

Struct patterns work in `let` too:

```
let Point(a, b) = get_position()
let Point(x = a, y = b) = get_position()
```

### Combine patterns inside other patterns

Patterns nest. You can put a variant pattern inside a tuple pattern, a tuple pattern inside a variant pattern, and so on. This is useful when you want to handle several pieces of state together:

```
// Both players have to be ready before the game starts
match (player1.status, player2.status) {
    (.Ready, .Ready) -> start_game()
    (.Ready, _) -> println("waiting for player 2")
    (_, .Ready) -> println("waiting for player 1")
    _ -> println("waiting for both players")
}
```

You can also peer into nested enums:

```
// Walk a linked list and pull out the head if it exists
match maybe_list {
    .some(.cons(head, _)) -> "first element is " .. head
    .some(.empty) -> "list is empty"
    .none -> "no list"
}
```

## Exhaustiveness — the compiler has your back

When you write a `match`, the compiler checks that you've covered every possible value. If you forget a variant, you get a clear error pointing at what's missing.

```
type Color = Red | Green | Blue

// Compile error: missing pattern .Blue
match c {
    .Red -> "stop"
    .Green -> "go"
}
```

This is one of the best things about patterns: refactoring becomes much safer. If you add a new variant to an enum, every `match` on that enum will tell you it needs to be updated. Use `_` as a catch-all when you genuinely want to ignore the rest, but reach for it sparingly — explicit cases are easier to maintain.
