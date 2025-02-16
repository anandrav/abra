use std::fs;

pub fn fread(path: String) -> String {
    fs::read_to_string(path).expect("Unable to read from file")
}
