use abra_core::*;
use criterion::{criterion_group, criterion_main, Criterion};

fn fib() {
    let src = "func fibonacci(n) {
        match n {
            0 -> 0
            1 -> 1
            _ -> fibonacci(n-1) + fibonacci(n-2)
        }
    }
    fibonacci(6)";
    let _ = compile::<side_effects::DefaultEffects>(source_files_single(src));
}

fn compile_benchmark(c: &mut Criterion) {
    c.bench_function("compile fib", |b| b.iter(|| fib()));
}

criterion_group!(benches, compile_benchmark);
criterion_main!(benches);
