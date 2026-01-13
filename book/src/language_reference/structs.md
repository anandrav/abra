# Structs

Define a `struct` to group together related pieces of data.

```
type Person = {
    first_name: string
    last_name: string
    age: int
}
```

Create an instance of a struct by calling its constructor, which is a function that shares the same name as the struct.

```
let frank = Person("Frank", "Smith", 34)
```

Access the fields of a struct and modify them by using dot `.` syntax.

```
let fullname = frank.first_name .. " " .. frank.last_name
// fullname = "Frank Smith"
frank.age = frank.age + 1
// age = 35
```

Structs can have generic type arguments.

```
type Ref<T> = {
    value: T
}
```