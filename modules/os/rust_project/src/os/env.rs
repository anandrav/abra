pub fn get_var(key: String) -> String {
    std::env::var(key).unwrap_or("".to_string())
}
