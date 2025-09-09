/// Appends formatted text directly into a `String`, like [`write!`],
/// but without returning a `Result`.
///
/// This macro is safe to use because writing to a `String` via
/// [`std::fmt::Write::write_fmt`] cannot fail. It avoids the
/// temporary allocation and verbosity that would occur with `push_str(&format!(...))`.
///
/// # Examples
///
/// ```
/// use utils::swrite;
///
/// let s = &mut String::new();
/// swrite!(s, "Hello {}", "world");
/// swrite!(s, ", number: {}", 123);
/// assert_eq!(s, "Hello world, number: 123");
/// ```
#[macro_export]
macro_rules! swrite {
    ($s:expr, $($arg:tt)*) => {{
        // Ensure we have a mutable borrow for write_fmt
        ::std::fmt::Write::write_fmt($s, format_args!($($arg)*)).unwrap()
    }};
}

#[cfg(test)]
mod tests {
    #[test]
    fn basic() {
        let s = &mut String::new();
        swrite!(s, "{}, {}, {}", "text", 123, 4.56);
        assert_eq!(s, "text, 123, 4.56");
    }
}
