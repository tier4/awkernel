//! VFS filesystem trait and associated types.
//!
//! Any concrete filesystem (FAT, RAM, etc.) implements `VfsFileSystem`.
//! Callers receive `Box<dyn VfsFile>` handles and never touch FAT internals.

use alloc::{boxed::Box, string::String, vec::Vec};

use super::{
    error::{VfsErrorKind, VfsResult},
    path::{VfsFileType, VfsMetadata},
};

/// Seek origin — mirrors `file::io::SeekFrom` so callers need not import
/// the internal I/O module.
pub use crate::file::io::SeekFrom as VfsSeekFrom;

// ── File handle ───────────────────────────────────────────────────────────────

/// An open file handle returned by the VFS.
///
/// All methods return `VfsResult` so the error type is uniform regardless of
/// the underlying filesystem.
pub trait VfsFile: Send {
    /// Read bytes into `buf`; returns the number read (0 = EOF).
    fn read(&mut self, buf: &mut [u8]) -> VfsResult<usize>;

    /// Write bytes from `buf`; returns the number written.
    fn write(&mut self, buf: &[u8]) -> VfsResult<usize>;

    /// Reposition the file cursor.
    fn seek(&mut self, pos: VfsSeekFrom) -> VfsResult<u64>;

    /// Flush pending writes to the underlying storage.
    fn flush(&mut self) -> VfsResult<()>;
}

// ── Directory entry ───────────────────────────────────────────────────────────

/// A single item returned by `VfsFileSystem::read_dir`.
pub struct VfsDirEntry {
    pub name: String,
    pub file_type: VfsFileType,
    /// File size in bytes; 0 for directories.
    pub size: u64,
}

// ── Filesystem trait ──────────────────────────────────────────────────────────

/// Abstract filesystem — the core of the VFS layer.
///
/// All path arguments are `/`-separated strings.  A leading `/` is ignored so
/// both `"/foo/bar.txt"` and `"foo/bar.txt"` resolve the same way.
pub trait VfsFileSystem: Send + Sync {
    /// Open an existing file for reading and writing.
    fn open_file(&self, path: &str) -> VfsResult<Box<dyn VfsFile>>;

    /// Create a file (truncates if it already exists).
    ///
    /// Intermediate directories must already exist.
    fn create_file(&self, path: &str) -> VfsResult<Box<dyn VfsFile>>;

    /// Remove a file or an empty directory.
    fn remove(&self, path: &str) -> VfsResult<()>;

    /// Create a directory.
    ///
    /// Succeeds even if the directory already exists.
    fn create_dir(&self, path: &str) -> VfsResult<()>;

    /// List entries inside a directory.
    fn read_dir(&self, path: &str) -> VfsResult<Vec<VfsDirEntry>>;

    /// Return metadata (type and size) for a path.
    fn metadata(&self, path: &str) -> VfsResult<VfsMetadata>;

    /// Rename or move a path.
    fn rename(&self, src: &str, dst: &str) -> VfsResult<()>;

    /// Check whether a path exists.
    fn exists(&self, path: &str) -> VfsResult<bool> {
        match self.metadata(path) {
            Ok(_) => Ok(true),
            Err(ref e) if matches!(e.kind(), VfsErrorKind::NotFound) => Ok(false),
            Err(e) => Err(e),
        }
    }
}
