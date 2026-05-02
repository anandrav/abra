# Enums

An enum is a type whose value is one of a fixed set of variants. Use them when a value can be one of a few distinct things — a color, a direction, the result of a network request, the kind of token a parser just read.

```
type Color =
    | Red
    | Green
    | Blue
```

Construct a variant by qualifying it with the enum name:

```
let c = Color.Red
```

When Abra can infer the enum type from context — a type annotation, a function parameter, a comparison against another value of the same enum — you can drop the prefix and write just the variant with a leading dot:

```
let c: Color = .Red

fn paint(c: Color) { ... }
paint(.Green)
```

If the type can't be inferred at the call site, the leading-dot form won't compile and you'll need to fully qualify the variant.

### Variants with data

Each variant can carry its own data. Construct one by passing the data as arguments, the same way you'd construct a struct:

```
type Shape =
    | Circle(float)
    | Rectangle(float, float)
    | Origin

let c = Shape.Circle(5.0)
let r = Shape.Rectangle(2.0, 4.0)
let o = Shape.Origin
```

Or with leading-dot syntax when the type is known from context:

```
fn area(s: Shape) -> float { ... }

area(.Circle(5.0))
area(.Rectangle(2.0, 4.0))
area(.Origin)
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
