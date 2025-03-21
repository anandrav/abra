// TODO: it would be easier to just make these .abra files instead of creating an entire helper crate just to define these string constants
pub const UTIL_ABRA: &str = r#"
host fn foo(a: int, b: int) -> int

"#;

pub const MAIN_ABRA: &str = r#"
use util

let x = foo(2, 3)
x + x
"#;
