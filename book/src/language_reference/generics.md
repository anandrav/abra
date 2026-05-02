# Generics

A generic type or function is one that works with many different types. Generics let you write code once and use it with any concrete type that fits.

### Type variables

A type variable is a placeholder that stands in for some real type. Type variables are written as a single uppercase letter, optionally followed by digits: `T`, `U`, `K`, `V`, `T2`. Identifiers like `Key` or `Item` are not type variables — they are ordinary names.

### Generic functions

A type variable in a function signature lets the function accept any type:

```
fn identity(x: T) -> T {
    x
}

let a = identity(5)         // T = int
let b = identity("hello")   // T = string
```

The type checker infers what `T` is at each call site.

### Generic types

Structs and enums can take type parameters in angle brackets:

```
type Pair<T> = {
    first: T
    second: T
}

type Either<A, B> =
    | Left(A)
    | Right(B)

let p = Pair(1, 2)              // Pair<int>
let e: Either<string, int> = .Left("oops")
```

### Interface constraints

A type variable can be constrained to types that implement particular interfaces. Constraints are written after the type variable, separated by spaces:

```
fn max(a: T Ord, b: T) -> T {
    if a > b { a } else { b }
}

fn print_pair(a: T ToString, b: T) {
    println(a .. " and " .. b)
}
```

Multiple constraints can be combined:

```
fn find_and_show(arr: array<T Equal ToString>, target: T) {
    if arr.contains(target) {
        println("found " .. target)
    }
}
```

The constraint applies to the type variable. Once you've constrained `T` once, you don't need to repeat the constraint on every parameter that uses `T`.

### Wildcard `_` in type annotations

When you only want to fix part of a generic type, write `_` for the parts the compiler should infer:

```
use core/map

let m: map<_, string> = map.new()  // key type inferred from later usage
m.insert(1, "hello")
m.insert(2, "world")
```

### Monomorphization

Each concrete instantiation of a generic function gets its own compiled copy. There is no runtime overhead for using generics.
