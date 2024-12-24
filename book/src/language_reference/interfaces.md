# Interfaces

An interface is a collection of functions that operate on a type named `self`.
An interface can be implemented for multiple types.
For instance, the `Number` interface supports the add, subtract, multiply, and divide operations.
The Number interface is implemented for both `int` and `float` type. The Number could be implemented for a user-defined type.

Example: Implementing the ToString interface for the Person struct
```
interface ToString {
    fn to_string(x: self) -> string
}

type Person = {
    first_name: string,
    last_name: string,
    age: int,
}

impl ToString for Person {
    fn to_string(x: Person) -> string {
        x.first_name & " " & x.last_name & ", " x.age & " years old."
    }
}
```