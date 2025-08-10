## Enums

Enums are useful for modeling data as a set of possible variants.

```
type Color =
  | Red
  | Blue
  | Green
```

Data can be associated with each variant of an enum

```
type Shape =
    | Circle(float)
    | Rectangle(float, float)
    | Triangle(float, float)
    
let circle = Shape.Circle(5.0)
let rect = Shape.Rectangle(2.0, 4.0)
```

Match expressions are used to handle each possible case of an enum.

```
let c = Shape.Circle(5.2)
let area = match c {
    .Circle(radius) -> radius * radius * pi,
    .Rectangle(width, height) -> width * height,
    .Triangle(width, height) -> width * height * 0.5,
}
```