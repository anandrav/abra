/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{error::Error, path::PathBuf};

use abra_core::OsFileProvider;

fn main() -> Result<(), Box<dyn Error>> {
    let this_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR")?);

    let file_provider = OsFileProvider::single_dir(this_dir.clone());

    let out_dir = PathBuf::from(std::env::var("OUT_DIR")?);
    let destination = out_dir;

    if let Err(s) =
        abra_core::generate_host_function_enum("host_funcs.abra", file_provider, &destination)
    {
        panic!("{}", s)
    }

    Ok(())
}
