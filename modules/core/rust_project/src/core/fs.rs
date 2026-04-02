/* This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/. */

use abra_core::vm::AbraInt;
use crate::ffi::core::fs::FsError;
use glob as glob_crate;
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

pub fn is_symlink(path: String) -> bool {
    Path::new(&path).is_symlink()
}

pub fn file_size(path: String) -> Result<AbraInt, FsError> {
    let meta = fs::metadata(&path).map_err(io_err)?;
    Ok(meta.len() as AbraInt)
}

pub fn modified_time(path: String) -> Result<f64, FsError> {
    let meta = fs::metadata(&path).map_err(io_err)?;
    let modified = meta.modified().map_err(io_err)?;
    let duration = modified
        .duration_since(std::time::UNIX_EPOCH)
        .map_err(|e| FsError::Other(e.to_string()))?;
    Ok(duration.as_secs_f64())
}

pub fn is_executable(path: String) -> Result<bool, FsError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let meta = fs::metadata(&path).map_err(io_err)?;
        Ok(meta.permissions().mode() & 0o111 != 0)
    }
    #[cfg(not(unix))]
    {
        let _ = fs::metadata(&path).map_err(io_err)?;
        Ok(true)
    }
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

// ── Symlinks ──

pub fn symlink(target: String, link_path: String) -> Result<(), FsError> {
    #[cfg(unix)]
    {
        std::os::unix::fs::symlink(&target, &link_path).map_err(io_err)
    }
    #[cfg(not(unix))]
    {
        std::os::windows::fs::symlink_file(&target, &link_path).map_err(io_err)
    }
}

pub fn read_link(path: String) -> Result<String, FsError> {
    fs::read_link(&path)
        .map(|p| p.to_string_lossy().to_string())
        .map_err(io_err)
}

// ── Permissions ──

pub fn set_executable(path: String, executable: bool) -> Result<(), FsError> {
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        let meta = fs::metadata(&path).map_err(io_err)?;
        let mut perms = meta.permissions();
        let mode = perms.mode();
        if executable {
            // Add execute bits for each read bit that's set
            let exec_bits = (mode & 0o444) >> 2;
            perms.set_mode(mode | exec_bits);
        } else {
            perms.set_mode(mode & !0o111);
        }
        fs::set_permissions(&path, perms).map_err(io_err)
    }
    #[cfg(not(unix))]
    {
        let _ = (&path, executable);
        Ok(())
    }
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

pub fn temp_file() -> Result<String, FsError> {
    let dir = std::env::temp_dir();
    let id = std::process::id();
    let time = std::time::SystemTime::now()
        .duration_since(std::time::UNIX_EPOCH)
        .unwrap_or_default()
        .as_nanos();
    let path = dir.join(format!("abra_tmp_{id}_{time}"));
    fs::File::create(&path).map_err(io_err)?;
    Ok(path.to_string_lossy().to_string())
}

// ── Batch file discovery ──

pub fn glob(pattern: String) -> Result<Vec<String>, FsError> {
    let paths =
        glob_crate::glob(&pattern).map_err(|e| FsError::Other(e.msg.to_string()))?;
    let mut result = Vec::new();
    for entry in paths {
        let path = entry.map_err(|e| io_err(e.into_error()))?;
        result.push(path.to_string_lossy().to_string());
    }
    Ok(result)
}

pub fn walk_dir(path: String) -> Result<Vec<String>, FsError> {
    let mut result = Vec::new();
    walk_dir_recursive(Path::new(&path), &mut result)?;
    Ok(result)
}

fn walk_dir_recursive(dir: &Path, result: &mut Vec<String>) -> Result<(), FsError> {
    let entries = fs::read_dir(dir).map_err(io_err)?;
    for entry in entries {
        let entry = entry.map_err(io_err)?;
        let path = entry.path();
        if path.is_dir() {
            walk_dir_recursive(&path, result)?;
        } else {
            result.push(path.to_string_lossy().to_string());
        }
    }
    Ok(())
}
