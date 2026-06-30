//! FAT filesystem adapter: wraps `fatfs::FileSystem` behind `VfsFileSystem`.
//!
//! Two concrete instantiations exist:
//!   * `FatVfs<BlockDeviceDisk, NullTimeProvider, LossyOemCpConverter>` — storage-backed
//!   * `FatVfs<InMemoryDisk,    NullTimeProvider, LossyOemCpConverter>` — in-memory
//!
//! Both are erased to `Arc<dyn VfsFileSystem>` in the global VFS singleton.

use alloc::{boxed::Box, vec::Vec};
use core::fmt::Debug;

use crate::file::{
    error::IoError,
    fatfs::{
        error::Error as FatError,
        file::File,
        fs::{FileSystem, OemCpConverter, ReadWriteSeek},
        time::TimeProvider,
    },
    io::{Read, Seek, Write},
    vfs::{
        error::{VfsError, VfsErrorKind, VfsIoError, VfsResult},
        filesystem::{VfsDirEntry, VfsFile, VfsFileSystem, VfsSeekFrom},
        path::{VfsFileType, VfsMetadata},
    },
};
use alloc::sync::Arc;

// ── Helpers ───────────────────────────────────────────────────────────────────

/// Convert a fatfs error to a VfsError, attaching the originating path.
fn fat_err<E>(err: FatError<E>, path: &str) -> VfsError
where
    E: Debug + IoError + Into<VfsIoError>,
{
    VfsError::from(VfsErrorKind::from(err)).with_path(path)
}

/// Strip a leading '/' so VFS paths can be passed directly to fatfs, which
/// expects paths relative to the directory it is called on.
#[inline]
fn rel(path: &str) -> &str {
    path.trim_start_matches('/')
}

// ── FatVfs ────────────────────────────────────────────────────────────────────

/// VFS adapter for any FAT filesystem.
///
/// Generic over `IO` (the block device), `TP` (time provider), and `OCC`
/// (OEM code-page converter) to support both storage-backed and in-memory
/// FAT instances without code duplication.
pub struct FatVfs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + 'static,
    IO::Error: Debug + IoError + Into<VfsIoError>,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    fs: Arc<FileSystem<IO, TP, OCC>>,
}

impl<IO, TP, OCC> FatVfs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + 'static,
    IO::Error: Debug + IoError + Into<VfsIoError>,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    pub fn new(fs: Arc<FileSystem<IO, TP, OCC>>) -> Self {
        FatVfs { fs }
    }
}

// ── FatVfsFile ────────────────────────────────────────────────────────────────

struct FatVfsFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + 'static,
    IO::Error: Debug + IoError + Into<VfsIoError>,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    file: File<IO, TP, OCC>,
}

impl<IO, TP, OCC> VfsFile for FatVfsFile<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + 'static,
    IO::Error: Debug + IoError + Into<VfsIoError>,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    fn read(&mut self, buf: &mut [u8]) -> VfsResult<usize> {
        self.file
            .read(buf)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    fn write(&mut self, buf: &[u8]) -> VfsResult<usize> {
        self.file
            .write(buf)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    /// `VfsSeekFrom` is a type alias for `file::io::SeekFrom`, so no conversion
    /// is needed — the value is passed directly to `File::seek`.
    fn seek(&mut self, pos: VfsSeekFrom) -> VfsResult<u64> {
        self.file
            .seek(pos)
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }

    fn flush(&mut self) -> VfsResult<()> {
        self.file
            .flush()
            .map_err(|e| VfsError::from(VfsErrorKind::from(e)))
    }
}

// ── VfsFileSystem implementation ──────────────────────────────────────────────

impl<IO, TP, OCC> VfsFileSystem for FatVfs<IO, TP, OCC>
where
    IO: ReadWriteSeek + Send + Debug + 'static,
    IO::Error: Debug + IoError + Into<VfsIoError>,
    TP: TimeProvider + Send + Sync + 'static,
    OCC: OemCpConverter + Send + Sync + 'static,
{
    fn open_file(&self, path: &str) -> VfsResult<Box<dyn VfsFile>> {
        let file = FileSystem::root_dir(&self.fs)
            .open_file(rel(path))
            .map_err(|e| fat_err(e, path))?;
        Ok(Box::new(FatVfsFile { file }))
    }

    fn create_file(&self, path: &str) -> VfsResult<Box<dyn VfsFile>> {
        let file = FileSystem::root_dir(&self.fs)
            .create_file(rel(path))
            .map_err(|e| fat_err(e, path))?;
        Ok(Box::new(FatVfsFile { file }))
    }

    fn remove(&self, path: &str) -> VfsResult<()> {
        FileSystem::root_dir(&self.fs)
            .remove(rel(path))
            .map_err(|e| fat_err(e, path))
    }

    fn create_dir(&self, path: &str) -> VfsResult<()> {
        FileSystem::root_dir(&self.fs)
            .create_dir(rel(path))
            .map(|_| ())
            .map_err(|e| fat_err(e, path))
    }

    fn read_dir(&self, path: &str) -> VfsResult<Vec<VfsDirEntry>> {
        let root = FileSystem::root_dir(&self.fs);
        let rel_path = rel(path);
        let dir = if rel_path.is_empty() {
            root
        } else {
            root.open_dir(rel_path).map_err(|e| fat_err(e, path))?
        };

        let mut entries = Vec::new();
        for r in dir.iter() {
            let e = r.map_err(|err| {
                VfsError::from(VfsErrorKind::from(err)).with_path(path)
            })?;
            entries.push(VfsDirEntry {
                name: e.file_name(),
                file_type: if e.is_dir() {
                    VfsFileType::Directory
                } else {
                    VfsFileType::File
                },
                size: e.len(),
            });
        }
        Ok(entries)
    }

    fn metadata(&self, path: &str) -> VfsResult<VfsMetadata> {
        let rel_path = rel(path);

        // Root directory has no DirEntry of its own.
        if rel_path.is_empty() {
            return Ok(VfsMetadata {
                file_type: VfsFileType::Directory,
                len: 0,
                created: None,
                modified: None,
                accessed: None,
            });
        }

        // Split "a/b/c.txt" → parent="a/b", name="c.txt" so we can call
        // find_entry (single component) on the correct directory.
        let (parent, name) = match rel_path.rfind('/') {
            Some(idx) => (&rel_path[..idx], &rel_path[idx + 1..]),
            None => ("", rel_path),
        };

        let root = FileSystem::root_dir(&self.fs);
        let dir = if parent.is_empty() {
            root
        } else {
            root.open_dir(parent).map_err(|e| fat_err(e, path))?
        };

        let entry = dir
            .find_entry(name, None, None)
            .map_err(|e| fat_err(e, path))?;

        Ok(VfsMetadata {
            file_type: if entry.is_dir() {
                VfsFileType::Directory
            } else {
                VfsFileType::File
            },
            len: entry.len(),
            created: None,
            modified: None,
            accessed: None,
        })
    }

    fn rename(&self, src: &str, dst: &str) -> VfsResult<()> {
        let root = FileSystem::root_dir(&self.fs);
        // Both src and dst are relative to root; passing &root twice is safe
        // because Dir::rename takes &self (shared borrow).
        root.rename(rel(src), &root, rel(dst))
            .map_err(|e| fat_err(e, src))
    }
}
