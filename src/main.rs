#[macro_use]
extern crate lalrpop_util;
extern crate abra;
extern crate regex;

use abra::parse;

fn main() {
    println!("fn main()");
    let to_parse = r#"
print("hello world")
"#;
    let parsed = parse(to_parse);
}
