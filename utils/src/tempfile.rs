use std::{
    fs::{self, OpenOptions},
    io,
    path::PathBuf,
    time::{SystemTime, UNIX_EPOCH},
};

pub struct TempFile {
    path: PathBuf,
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

impl TempFile {
    pub fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();

        let path = std::env::temp_dir().join(format!("temp-{}-{nonce}.txt", std::process::id(),));

        Self { path }
    }
}

#[test]
fn basic() -> io::Result<()> {
    let path = {
        let temp = TempFile::new();
        fs::write(&temp.path, "test input\n")?;

        // Pass &temp.0 to the code you're testing.
        let contents = fs::read_to_string(&temp.path)?;
        assert_eq!(contents, "test input\n");

        temp.path.clone()
    };

    assert!(!fs::exists(path)?);

    Ok(())
}
