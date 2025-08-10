# Interfaces

An interface is a set of operations supported by some type named `self`.

A type implements an interface if it supports all its operations.
As an example, the `Num` interface supports the `add()`, `subtract()`, `multiply()`, and `divide()` operations.
The Number interface is implemented by both the `int` and `float` built-in types.

```
// support conversion to string
interface ToString {
    fn to_string(x: self) -> string
}

type Person = {
    first_name: string,
    last_name: string,
    age: int,
}

// support conversion to string for the Person type
impl ToString for Person {
    fn to_string(x: Person) -> string {
        x.first_name & " " & x.last_name & ", " x.age & " years old."
    }
}

...

let p = Person("Arthur", "Pendragon", 15)
let s = p.to_string() // "Arthur Pendragon 15"

```