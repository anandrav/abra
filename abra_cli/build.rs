/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{error::Error, path::PathBuf};

use abra_core::OsFileProvider;

fn main() -> Result<(), Box<dyn Error>> {
    let this_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());

    let file_provider = OsFileProvider::new(this_dir.clone(), PathBuf::new(), PathBuf::new());

    let destination = this_dir.join("src").join("host_funcs.rs");

    abra_core::generate_host_function_enum("host_funcs.abra", file_provider, &destination)?;

    Ok(())
}
