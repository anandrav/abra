use std::{
    fs,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT_ID: AtomicU64 = AtomicU64::new(0);

pub struct TempFile {
    pub path: PathBuf,
}

impl Drop for TempFile {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.path);
    }
}

impl TempFile {
    pub fn new() -> Self {
        let nonce = NEXT_ID.fetch_add(1, Ordering::Relaxed);

        let path = std::env::temp_dir().join(format!("temp-{}-{nonce}.txt", std::process::id(),));

        Self { path }
    }
}

impl Default for TempFile {
    fn default() -> Self {
        Self::new()
    }
}

#[test]
fn basic() -> std::io::Result<()> {
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
