# Generics

A generic function or type works with many different types. Instead of writing one `identity` for `int` and another for `string`, write one that works for any type:

```
fn identity(x: T) -> T {
    x
}

let a = identity(5)         // T is int
let b = identity("hello")   // T is string
```

The `T` is a **type variable** — a placeholder that stands in for whatever real type the caller uses. Abra figures out what `T` should be at each call site.

By convention, type variables are a single uppercase letter, optionally followed by digits: `T`, `U`, `K`, `V`, `T2`. Names like `Item` or `Key` aren't type variables — they'd be parsed as ordinary identifiers.

### Generic types

Structs and enums can take type parameters too. Put them in angle brackets after the name:

```
type Pair<T> = {
    first: T
    second: T
}

type Either<A, B> =
    | Left(A)
    | Right(B)

let p = Pair(1, 2)                          // Pair<int>
let e: Either<string, int> = .Left("oops")
```

### Constraints

A generic function can require its type variable to support certain operations. You spell that out with an interface constraint:

```
fn max(a: T Ord, b: T) -> T {
    if a > b { a } else { b }
}
```

The `T Ord` says "any type, as long as it implements `Ord`". This lets you use `>` on `a` and `b` inside the body.

You can list multiple constraints:

```
fn find_and_show(arr: array<T Equal ToString>, target: T) {
    if arr.contains(target) {
        println("found " .. target)
    }
}
```

You only need to write the constraint once. Other parameters that mention the same `T` automatically get the same constraints.

### Wildcards in type annotations

Sometimes you only want to fix part of a generic type and let the compiler figure out the rest. Use `_` for the parts to infer:

```
use core/map

let m: map<_, string> = map.new()    // key type filled in below
m.insert(1, "hello")
m.insert(2, "world")
```

### Performance

Each combination of type arguments gets its own compiled copy of the function — there's no runtime cost to using generics. (This is called *monomorphization* if you want a name for it.)
