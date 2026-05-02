# Interfaces

An interface is a contract: a set of methods that a type can support. Once a type implements an interface, you can use it anywhere that interface is required. If you've used traits in Rust or typeclasses in Haskell, this should feel familiar.

A simple example: the `ToString` interface says "I know how to convert myself to a string". Lots of types implement it — `int`, `bool`, `array<T>`, and so on. That's why `println` and the `..` operator can take values of any of those types.

### Implementing an interface

Define an interface with `interface`. Implement it for a specific type with `implement`.

```
interface ToString {
    fn str(self) -> string
}

type Person = {
    first_name: string
    last_name: string
    age: int
}

implement ToString for Person {
    fn str(self) -> string {
        self.first_name .. " " .. self.last_name .. ", " .. self.age
    }
}

let p = Person("Arthur", "Pendragon", 15)
println(p.str())     // "Arthur Pendragon, 15"
println("Hi, " .. p) // "Hi, Arthur Pendragon, 15" — `..` uses ToString
```

The first parameter is `self` and refers to the value the method is called on. You don't need to write its type — it's inferred to be the type you're implementing for.

## Interfaces in the prelude

Abra's prelude defines a handful of interfaces that the language itself relies on. Implementing them makes your types work with familiar syntax — operators, `for` loops, indexing, and so on.

### ToString

Convert a value to a string. The `..` operator and `println` use this:

```
let arr = [1, 2, 3]
println("got " .. arr)         // "got [ 1, 2, 3 ]"
```

### Equal

Compare two values for equality with `==` and `!=`. Implement it on your own type to make it comparable:

```
implement Equal for Point {
    fn equal(a, b) {
        a.x == b.x and a.y == b.y
    }
}
```

### Ord

Defines `<`, `<=`, `>`, `>=`. Required by methods like `array.sort()`.

### Num

Powers `+`, `-`, `*`, `/`, `^`. Implemented for `int` and `float`. (You usually wouldn't implement this for your own types, but you can.)

### Clone

Make a deep copy of a value:

```
let arr = [1, 2, 3]
let arr2 = arr.clone()
arr2.pop()
arr2.pop()
arr2.pop()
// arr  = [1, 2, 3]
// arr2 = []
```

### Hash

Required for any type used as a map or set key.

### Iterable and Iterator

Make your type usable in a `for` loop. `Iterable` produces an `Iterator`, which yields one value at a time. The built-in `array<T>`, `range`, and `int` all implement `Iterable` — that's why you can write `for x in [1, 2, 3]` or `for i in 5`.

If you want to iterate over a custom container, implement these. See [Output types](#output-types) below for the details.

### Index

Powers `x[i]` and `x[i] = v`. Implemented for `array<T>`, `map`, and `JsonValue`.

### Unwrap and Try

Power the `!` and `?` operators. Both are implemented for `option` and `result`.

## Output types

Some interfaces have a method whose return type depends on the implementing type. The `Iterable` interface is the classic case — different containers produce different kinds of iterators. An `array<T>` makes an `ArrayIterator<T>`; a hypothetical `tree<T>` would make a `TreeIterator<T>`. They're not the same type, but each one is a valid iterator.

Abra handles this with **output types**. An interface declares one or more `outputtype`s, and each implementation fills them in.

```
interface Iterable {
    outputtype IterableItem
    outputtype Iter impl Iterator<IteratorItem=IterableItem>

    fn make_iterator(self) -> Iter
}

interface Iterator {
    outputtype IteratorItem

    fn next(self) -> option<IteratorItem>
}
```

Without output types, an interface like `Iterable` would have to be parameterized over both the item type and the iterator type, which would mean a lot more type annotations everywhere it's used.
