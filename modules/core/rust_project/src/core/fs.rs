/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use crate::ffi::core::fs::FsError;
use std::fs::{self, OpenOptions};
use std::io::{self, Write};
use std::path::Path;

fn io_err(e: io::Error) -> FsError {
    let msg = e.to_string();
    match e.kind() {
        io::ErrorKind::NotFound => FsError::NotFound(msg),
        io::ErrorKind::PermissionDenied => FsError::PermissionDenied(msg),
        io::ErrorKind::AlreadyExists => FsError::AlreadyExists(msg),
        _ => FsError::Other(msg),
    }
}

// ── File I/O ──

pub fn read(path: String) -> Result<String, FsError> {
    fs::read_to_string(&path).map_err(io_err)
}

pub fn write(path: String, content: String) -> Result<(), FsError> {
    fs::write(&path, content).map_err(io_err)
}

pub fn append(path: String, content: String) -> Result<(), FsError> {
    let mut file = OpenOptions::new()
        .create(true)
        .append(true)
        .open(&path)
        .map_err(io_err)?;
    writeln!(file, "{content}").map_err(io_err)
}

pub fn copy(src: String, dest: String) -> Result<(), FsError> {
    fs::copy(&src, &dest).map(|_| ()).map_err(io_err)
}

pub fn rename(old_path: String, new_path: String) -> Result<(), FsError> {
    fs::rename(&old_path, &new_path).map_err(io_err)
}

pub fn remove(path: String) -> Result<(), FsError> {
    fs::remove_file(&path).map_err(io_err)
}

pub fn exists(path: String) -> Result<bool, FsError> {
    fs::exists(&path).map_err(io_err)
}

// ── Directory operations ──

pub fn mkdir(path: String) -> Result<(), FsError> {
    fs::create_dir(&path).map_err(io_err)
}

pub fn mkdir_all(path: String) -> Result<(), FsError> {
    fs::create_dir_all(&path).map_err(io_err)
}

pub fn rmdir(path: String) -> Result<(), FsError> {
    fs::remove_dir(&path).map_err(io_err)
}

pub fn rmdir_all(path: String) -> Result<(), FsError> {
    fs::remove_dir_all(&path).map_err(io_err)
}

pub fn list_dir(path: String) -> Result<Vec<String>, FsError> {
    let entries = fs::read_dir(&path).map_err(io_err)?;
    let mut result = Vec::new();
    for entry in entries {
        let entry = entry.map_err(io_err)?;
        result.push(entry.path().to_string_lossy().to_string());
    }
    Ok(result)
}

// ── Metadata ──

pub fn is_file(path: String) -> bool {
    Path::new(&path).is_file()
}

pub fn is_dir(path: String) -> bool {
    Path::new(&path).is_dir()
}

// ── Path manipulation ──

pub fn join(base: String, child: String) -> String {
    Path::new(&base).join(&child).to_string_lossy().to_string()
}

pub fn parent(path: String) -> Option<String> {
    Path::new(&path).parent().map(|p| p.to_string_lossy().to_string())
}

pub fn filename(path: String) -> Option<String> {
    Path::new(&path).file_name().map(|s| s.to_string_lossy().to_string())
}

pub fn extension(path: String) -> Option<String> {
    Path::new(&path).extension().map(|s| s.to_string_lossy().to_string())
}

pub fn stem(path: String) -> Option<String> {
    Path::new(&path).file_stem().map(|s| s.to_string_lossy().to_string())
}

pub fn absolute(path: String) -> Result<String, FsError> {
    fs::canonicalize(&path)
        .map(|p| p.to_string_lossy().to_string())
        .map_err(io_err)
}

// ── Environment ──

pub fn getcwd() -> Result<String, FsError> {
    std::env::current_dir()
        .map(|p| p.to_string_lossy().to_string())
        .map_err(io_err)
}

pub fn temp_dir() -> String {
    std::env::temp_dir().to_string_lossy().to_string()
}
