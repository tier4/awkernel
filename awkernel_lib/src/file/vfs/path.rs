//! Virtual filesystem path
//!
//! The virtual file system abstraction generalizes over file systems and allow using
//! different VirtualFileSystem implementations (i.e. an in memory implementation for unit tests)

use super::super::error::IoError;
use super::super::io::{Read, Seek, Write};
use crate::time::Time;
use alloc::{
    string::{String, ToString},
    vec::Vec,
};

use super::error::VfsErrorKind;
use super::{error::VfsError, error::VfsResult};

/// Trait combining Seek and Read, return value for opening files
pub trait SeekAndRead: Seek + Read {}

/// Trait combining Seek and Write, return value for writing files
pub trait SeekAndWrite: Seek + Write {}

impl<T> SeekAndRead for T where T: Seek + Read {}

impl<T> SeekAndWrite for T where T: Seek + Write {}

/// A trait for common non-async behaviour of both sync and async paths
pub trait PathLike: Clone {
    type Error: IoError;
    fn get_path(&self) -> String;
    fn filename_internal(&self) -> String {
        let path = self.get_path();
        let index = path.rfind('/').map(|x| x + 1).unwrap_or(0);
        path[index..].to_string()
    }

    fn extension_internal(&self) -> Option<String> {
        let filename = self.filename_internal();
        let mut parts = filename.rsplitn(2, '.');
        let after = parts.next();
        let before = parts.next();
        match before {
            None | Some("") => None,
            _ => after.map(|x| x.to_string()),
        }
    }

    fn parent_internal(&self, path: &str) -> String {
        let index = path.rfind('/');
        index.map(|idx| path[..idx].to_string()).unwrap_or_default()
    }

    fn join_internal(&self, in_path: &str, path: &str) -> VfsResult<String, Self::Error> {
        if path.is_empty() {
            return Ok(in_path.to_string());
        }
        let mut new_components: Vec<&str> = Vec::with_capacity(
            in_path.chars().filter(|c| *c == '/').count()
                + path.chars().filter(|c| *c == '/').count()
                + 1,
        );
        let mut base_path = if path.starts_with('/') {
            "".to_string()
        } else {
            in_path.to_string()
        };
        // Prevent paths from ending in slashes unless this is just the root directory.
        if path.len() > 1 && path.ends_with('/') {
            return Err(VfsError::from(VfsErrorKind::InvalidPath).with_path(path));
        }
        for component in path.split('/') {
            if component == "." || component.is_empty() {
                continue;
            }
            if component == ".." {
                if !new_components.is_empty() {
                    new_components.truncate(new_components.len() - 1);
                } else {
                    base_path = self.parent_internal(&base_path);
                }
            } else {
                new_components.push(component);
            }
        }
        let mut path = base_path;
        path.reserve(
            new_components.len()
                + new_components
                    .iter()
                    .fold(0, |accum, part| accum + part.len()),
        );
        for component in new_components {
            path.push('/');
            path.push_str(component);
        }
        Ok(path)
    }
}

/// Type of file
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VfsFileType {
    /// A plain file
    File,
    /// A Directory
    Directory,
}

/// File metadata information
#[derive(Debug)]
pub struct VfsMetadata {
    /// The type of file
    pub file_type: VfsFileType,
    /// Length of the file in bytes, 0 for directories
    pub len: u64,
    /// Creation time of the file, if supported by the vfs implementation
    pub created: Option<Time>,
    /// Modification time of the file, if supported by the vfs implementation
    pub modified: Option<Time>,
    /// Access time of the file, if supported by the vfs implementation
    pub accessed: Option<Time>,
}
