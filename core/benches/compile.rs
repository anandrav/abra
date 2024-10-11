use criterion::{black_box, criterion_group, criterion_main, Criterion};
use abra_core::compile_bytecode;
use abra_core::effects::DefaultEffects;
use abra_core::effects::EffectTrait;
use abra_core::source_files_single;
use abra_core::vm::Vm;

pub fn criterion_benchmark(c: &mut Criterion) {
    let src = r#"
fn fib(n) {
    match n {
        0 -> 0
        1 -> 1
        _ -> fib(n-1) + fib(n-2)
    }
}   
fib(10) 
"#;
    c.bench_function("compile", |b| b.iter(|| {
      let sources = source_files_single(src);
      let program = compile_bytecode(sources, DefaultEffects::enumerate()).unwrap(); 
      black_box(program);
    }));
}

criterion_group!(benches, criterion_benchmark);
criterion_main!(benches);
