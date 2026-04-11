use std::sync::atomic::AtomicBool;

pub static DEBUG_LOG: AtomicBool = AtomicBool::new(false);

#[macro_export]
macro_rules! dlog {
    ($($arg:tt)*) => {{
        // Must be debug build *and* the DEBUG_LOG global must be enabled
        if cfg!(debug_assertions) {
            if $crate::log::DEBUG_LOG.load(::std::sync::atomic::Ordering::Relaxed) {
                print!("[abra debug] ");
                println!($($arg)*);
            }
        }
    }};
}
