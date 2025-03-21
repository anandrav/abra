pub const UTIL_ABRA: &str = r#"
fn foo(a: int, b) {
  a + b
}
"#;

pub const MAIN_ABRA: &str = r#"
use util

fn bar(x: 'a) -> 'a {
  x
}

foo(2, 2)
"#;
