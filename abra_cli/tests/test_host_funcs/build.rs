use std::{collections::HashMap, error::Error, path::PathBuf};

use abra_core::{
    MockFileProvider,
    effects::{DefaultEffects, EffectTrait},
};
use test_host_funcs_helper::*;

fn main() -> Result<(), Box<dyn Error>> {
    let mut files: HashMap<PathBuf, String> = HashMap::new();
    files.insert("main.abra".into(), MAIN_ABRA.into());
    files.insert("util.abra".into(), UTIL_ABRA.into());
    let file_provider = MockFileProvider::new(files);

    let this_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let destination = PathBuf::from(this_dir).join("src").join("host_funcs.rs");

    abra_core::generate_host_function_enum(
        "main.abra",
        DefaultEffects::enumerate(),
        file_provider,
        &destination,
    )?;

    Ok(())
}
