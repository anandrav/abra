pub mod env;
pub mod exec;

use std::fs::{self, OpenOptions};
use std::io::Write;

pub fn fread(path: String) -> Result<String, String> {
    // println!("fn fread({path})");
    fs::read_to_string(path).map_err(|e| e.to_string())
}

pub fn fwrite(path: String, content: String) {
    // println!("fn fwrite({path}, {content})");
    fs::write(path, content).expect("Unable to write to file");
}

pub fn fexists(path: String) -> bool {
    // println!("fn fexists({path})");
    fs::exists(path).unwrap()
}

pub fn fremove(path: String) {
    // println!("fn fremove({path})");
    fs::remove_file(path).unwrap()
}

pub fn frename(old_path: String, new_path: String) {
    // println!("fn frename({old_path}, {new_path})");
    fs::rename(old_path, new_path).unwrap();
}

pub fn fcopy(src: String, dest: String) {
    // println!("fn fcopy({src}, {dest})");
    fs::copy(src, dest).unwrap();
}

pub fn fappend(path: String, content: String) {
    // println!("fn fappend({path}, {content})");
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(path)
        .unwrap();

    // Write the text followed by a newline.
    writeln!(file, "{}", content).unwrap();
}
