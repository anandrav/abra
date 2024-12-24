## Enums

Define an `enum` to represent a set of possibilities.
```
type Color =
    Red
  | Blue
  | Green
```

Data can optionally be associated with each variant of an enum type.
```
type Shape =
    | Circle(float)
    | Rectangle(float, float)
    | Triangle(float, float)
```

Given an enum, its value can be inspected by using a match expression.
The associated data for a variant can be bound to a variable using the `~` syntax.
```
let c = Circle(5.2)
let area = match c {
    Circle(~radius) -> radius * radius * pi,
    Rectangle(~width, ~height) -> width * height,
    Triangle(~width, ~height) -> width * height * 0.5,
}
```