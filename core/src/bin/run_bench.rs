use abra_core::*;

fn main() {
    let src = "func fibonacci(n) {
        match n {
            0 -> 0
            1 -> 1
            _ -> fibonacci(n-1) + fibonacci(n-2)
        }
    }
    fibonacci(20)";
    let _ = run(src).unwrap();
}
