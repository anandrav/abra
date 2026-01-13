# Interfaces

An interface is a set of operations supported by some type named `self`.

A type implements an interface if it supports all its operations.
As an example, the `Num` interface supports the `add()`, `subtract()`, `multiply()`, `divide()`, and `power()` operations.
The Number interface is implemented by both the `int` and `float` built-in types.

```
// support conversion to string
interface ToString {
    fn str(x: self) -> string
}

type Person = {
    first_name: string
    last_name: string
    age: int
}

// support conversion to string for the Person type
implement ToString for Person {
    fn str(x: Person) -> string {
        x.first_name .. " " .. x.last_name .. ", " x.age .. " years old."
    }
}

...

let p = Person("Arthur", "Pendragon", 15)
let s = p.str() // "Arthur Pendragon 15"

```

### Standard library interfaces

#### ToString

The ToString interface allows you to convert some type to a string.
Any type which implements the ToString interface can be passed as an argument to the `..` operator.

```
let arr = [1, 2, 3]
let arr_str = arr.str()         // arr_str = "[1, 2, 3]"
let age = 23
let name = "John"
println(name .. " is " .. age)    // prints "John is 23"
```

#### Clone

The clone interface allows you to create a deep copy of some data structure.
For instance, cloning an array allows you to manipulate its copy without manipulating the original.

```
let arr = [1, 2, 3]
let arr2 = arr.clone()
arr2.pop()
arr2.pop()
arr2.pop()
// arr = [1, 2, 3] and arr = []
```

#### Equal

The `Equal` interface is used to compare values for equality.
Types which implement the `Equal` interface can be compared for equality using the `=` operator.

#### Num

The `Num` interface is used for `int` and `float`.
Types which implement the `Num` interface can use the arithmetic operators.

#### Iterator

The `Iterator` interface is implemented by types which traverse over some data structure's elements.
The `Iterator` interface is used by the `Iterable` interface, but `Iterator` can also be used on its own.

#### Iterable

The `Iterable` interface is implemented for container types in order to iterate through their values.
Types which implement the Iterable interface can be used in a for loop. Types which implement the `Iterable` interface,
such as `array<T>`, have an _output type_ which implements
the `Iterator` interface. In the case of `array<T>`, that iterator type is `ArrayIterator<T>`.

### Output types

Output types are used when the output of an interface's operations are determined by the type of the input.
For instance, when implementing the `Iterable` interface, different container types will output different
iterator types.
For example, `array<T>` returns an `ArrayIterator<T>`, whereas a `hashmap<K,V>` would return a
`HashmapIterator<K,V>`, which is a completely different struct.
Similarly, a `StringIterator`, when implementing the `Iterator` interface, would always return a `maybe<char,void>`, so
`Item` = `char` in that case.

Without output types, interfaces like `Iterable` would have to be parameterized over `Item` and `Iter`,
which would require much more type annotations. This would also impede language features like operator overloading and
the `for-in` loop, which lean on interfaces in the prelude such as `Iterable` and `Iterator`.

```
interface Iterable {
    outputtype Item
    outputtype Iter impl Iterator<Item=Item>

    fn make_iterator: (Self) -> Iter
}

interface Iterator {
    outputtype Item

    fn next: (Self) -> maybe<Item,void>
}
```