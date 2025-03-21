use std::{error::Error, path::PathBuf};

use abra_core::{
    OsFileProvider,
    effects::{DefaultEffects, EffectTrait},
};

fn main() -> Result<(), Box<dyn Error>> {
    let abra_src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("abra_src");
    let file_provider = OsFileProvider::new(abra_src_dir, PathBuf::new(), PathBuf::new());

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
