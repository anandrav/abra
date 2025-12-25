/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use std::{error::Error, path::PathBuf};

use abra_core::OsFileProvider;

fn main() -> Result<(), Box<dyn Error>> {
    let abra_src_dir = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap()).join("abra_src");
    let file_provider = OsFileProvider::new(abra_src_dir, PathBuf::new(), vec![]); // TODO: passing dummies here is strange

    let this_dir = std::env::var("CARGO_MANIFEST_DIR").unwrap();
    let destination = PathBuf::from(this_dir).join("src");

    if let Err(s) = abra_core::generate_host_function_enum("util.abra", file_provider, &destination)
    {
        panic!("{}", s)
    }

    Ok(())
}
