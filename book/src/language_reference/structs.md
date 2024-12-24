# Structs

Define a `struct` to group together related pieces of data.
```
type Person = {
    first_name: string,
    last_name: string,
    age: int,
}
```

Create an instance of a struct by calling the struct as a function.
```
let frank = Person("Frank", "Smith", 34)
```

Access members of a struct and modify them by using dot `.` syntax.
```
let fullname = frank.first_name & " " & frank.last_name
frank.age = frank.age + 1
```