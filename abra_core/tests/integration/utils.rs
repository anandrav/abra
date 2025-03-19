// functions used for testing

use std::fmt::Display;

pub fn unwrap_or_panic<T, E: Display>(result: Result<T, E>) -> T {
    match result {
        Ok(value) => value,
        Err(e) => {
            eprintln!("Error: {}", e);
            panic!("Exiting due to error.");
        }
    }
}
