pub fn get_var(key: String) -> String {
    println!("fn get_var({key})");
    std::env::var(key).unwrap_or("".to_string())
}
