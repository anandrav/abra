# Interfaces

An interface is a set of operations supported by some type named `self`.

A type implements an interface if it supports all its operations.
As an example, the `Num` interface supports the `add()`, `subtract()`, `multiply()`, and `divide()` operations.
The Number interface is implemented by both the `int` and `float` built-in types.

```
// support conversion to string
interface ToString {
    fn str(x: self) -> string
}

type Person = {
    first_name: string,
    last_name: string,
    age: int,
}

// support conversion to string for the Person type
impl ToString for Person {
    fn str(x: Person) -> string {
        x.first_name & " " & x.last_name & ", " x.age & " years old."
    }
}

...

let p = Person("Arthur", "Pendragon", 15)
let s = p.str() // "Arthur Pendragon 15"

```

### Standard library interfaces

#### ToString

The ToString interface allows you to convert some type to a string.
Any type which implements the ToString interface can be passed as an argument to the `&` operator.

```
let arr = [1, 2, 3]
let arr_str = arr.str()         // arr_str = "[1, 2, 3]"
let age = 23
let name = "John"
println(name & " is " & age)    // prints "John is 23"
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

The equal interface is used to compare values for equality.
Types which implement the Equal interface can be compared for equality using the `=` operator.

#### Num

The Num interface is used for `int` and `float`.
Types which implement the Num interface can use the arithmetic operators.

#### Iterable

The Iterable interface is implemented for container types in order to iterate through their values.
Types which implement the Iterable interface can be used in a for loop.

#### Iterable

Types which implement the Iterable interface, such as `array<'T>`, have an associated type which implements
the Iterator interface. In the case of `array<'T>`, that type is `ArrayIterator<'T>`

### Associated types

- TODO