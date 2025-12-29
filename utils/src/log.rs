#[macro_export]
macro_rules! dlog {
    ($($arg:tt)*) => {{
        // Must be debug build *and* DEBUG_LOG must be defined in env
        if cfg!(debug_assertions) {
            if ::std::env::var("DEBUG_LOG").is_ok() {
                println!($($arg)*)
            }
        }
    }};
}
