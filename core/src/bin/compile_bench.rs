use abra_core::*;

fn main() {
    let src = r#"println("Enter your name: ")
    let name = read()
    println("Your name is " & name)

    func fibonacci(n) {
        match n {
            0 -> 0
            1 -> 1
            _ -> fibonacci(n-1) + fibonacci(n-2)
        }
    }

    let list = range(0,9)
    println("numbers: ")
    println(list)

    let list = map(list, fibonacci)
    println("fibonacci: ")
    println(list)

    let list = map(list, x -> x ^ 3)
    println("cubed: ")
    println(list)

    let list = filter(list, x -> x mod 2 = 1)
    println("only odds: ")
    println(list)

    let list = map(list, x -> to_float(x) * 3.14)
    println("times pi: ")
    println(list)

    print(newline)
    print("they add up to: ")
    println(sumf(list))"#;
    let _ = compile::<side_effects::DefaultEffects>(source_files_single(src)).unwrap();
}
