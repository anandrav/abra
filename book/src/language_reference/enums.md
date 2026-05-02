# Enums

An enum is a type whose value is one of a fixed set of variants. Use them when a value can be one of a few distinct things — a color, a direction, the result of a network request, the kind of token a parser just read.

```
type Color =
    | Red
    | Green
    | Blue
```

Construct a value with leading-dot syntax:

```
let c = .Red
```

### Variants with data

Each variant can carry its own data:

```
type Shape =
    | Circle(float)
    | Rectangle(float, float)
    | Origin

let c = .Circle(5.0)
let r = .Rectangle(2.0, 4.0)
let o = .Origin
```

### Handling all the variants

Use `match` to do something different for each case. The compiler checks that you've covered every variant, so you can't forget one:

```
let pi = 3.14159

fn area(s: Shape) -> float {
    match s {
        .Circle(r) -> pi * r * r
        .Rectangle(w, h) -> w * h
        .Origin -> 0.0
    }
}
```

If you later add a new variant to `Shape`, every `match` on `Shape` will start failing to compile until you handle it. That's exactly what you want.

### Generic enums

Enums can take type parameters too. The standard library uses this for `option` and `result`:

```
type option<T> =
    | some(T)
    | none

type result<T, E> =
    | ok(T)
    | err(E)
```

These two come up everywhere — see [Error Handling](./error_handling.md).
