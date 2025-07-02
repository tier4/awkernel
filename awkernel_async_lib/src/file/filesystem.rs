//! The async filesystem trait definitions needed to implement new async virtual filesystems
use super::path::AsyncVfsPath;
use crate::time::Time;
use alloc::{boxed::Box, string::String};
use async_trait::async_trait;
use awkernel_lib::file::{
    error::IoError,
    io::SeekFrom,
    vfs::error::{VfsError, VfsErrorKind, VfsResult},
    vfs::path::VfsMetadata,
};
use futures::stream::Stream;

// NOTE: We're currently using our own AsyncSeekAndRead and AsyncSeekAndWrite traits. We might replace these with traits from embedded-io-async in the future. However, that change would involve many modifications, and embedded-io-async doesn't seem stable yet, so we're sticking with our current approach for now.
#[async_trait]
pub trait AsyncSeekAndRead<E: IoError>: Send + Unpin {
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize>;

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64>;

    async fn read_exact(&mut self, mut buf: &mut [u8]) -> Result<()> {
        while !buf.is_empty() {
            match self.read(buf).await {
                Ok(0) => return Ok(()),
                Ok(n) => {
                    buf = &mut buf[n..];
                }
                Err(e) => return Err(e),
            }
        }

        Ok(())
    }
}

#[async_trait]
pub trait AsyncSeekAndWrite<E: IoError>: Send + Unpin {
    async fn write(&mut self, buf: &[u8]) -> Result<usize>;

    async fn write_all(&mut self, buf: &[u8]) -> Result<()>;

    async fn flush(&mut self) -> Result<()>;

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64>;
}

#[async_trait]
impl<E: IoError + Send> AsyncSeekAndRead<E> for Box<dyn AsyncSeekAndRead<E> + Send + Unpin> {
    async fn read(&mut self, buf: &mut [u8]) -> Result<usize> {
        (**self).read(buf).await
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        (**self).seek(pos).await
    }

    async fn read_exact(&mut self, buf: &mut [u8]) -> Result<()> {
        (**self).read_exact(buf).await
    }
}

#[async_trait]
impl<E: IoError + Send> AsyncSeekAndWrite<E> for Box<dyn AsyncSeekAndWrite<E> + Send + Unpin> {
    async fn write(&mut self, buf: &[u8]) -> Result<usize> {
        (**self).write(buf).await
    }

    async fn write_all(&mut self, buf: &[u8]) -> Result<()> {
        (**self).write_all(buf).await
    }

    async fn flush(&mut self) -> Result<()> {
        (**self).flush().await
    }

    async fn seek(&mut self, pos: SeekFrom) -> Result<u64> {
        (**self).seek(pos).await
    }
}

/// File system implementations must implement this trait
/// All path parameters are absolute, starting with '/', except for the root directory
/// which is simply the empty string (i.e. "")
/// The character '/' is used to delimit directories on all platforms.
/// Path components may be any UTF-8 string, except "/", "." and ".."
///
/// Please use the test_macros [test_macros::test_async_vfs!] and [test_macros::test_async_vfs_readonly!]
#[async_trait]
pub trait AsyncFileSystem: Sync + Send + 'static {
    /// The error type that can be returned by this file system.

    /// Iterates over all direct children of this directory path
    /// NOTE: the returned String items denote the local bare filenames, i.e. they should not contain "/" anywhere
    async fn read_dir(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn Unpin + Stream<Item = String> + Send>>;

    /// Creates the directory at this path
    ///
    /// Note that the parent directory must already exist.
    async fn create_dir(&self, path: &str) -> VfsResult<()>;

    /// Opens the file at this path for reading
    async fn open_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndRead<Self::IOError> + Send + Unpin>>;

    /// Creates a file at this path for writing
    async fn create_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite<Self::IOError> + Send + Unpin>>;

    /// Opens the file at this path for appending
    async fn append_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn AsyncSeekAndWrite<Self::IOError> + Send + Unpin>>;

    /// Returns the file metadata for the file at this path
    async fn metadata(&self, path: &str) -> VfsResult<VfsMetadata>;

    /// Sets the files creation timestamp, if the implementation supports it
    async fn set_creation_time(&self, _path: &str, _time: Time) -> VfsResult<()> {
        Err(VfsError::from(VfsErrorKind::NotSupported))
    }
    /// Sets the files modification timestamp, if the implementation supports it
    async fn set_modification_time(&self, _path: &str, _time: Time) -> VfsResult<()> {
        Err(VfsError::from(VfsErrorKind::NotSupported))
    }
    /// Sets the files access timestamp, if the implementation supports it
    async fn set_access_time(&self, _path: &str, _time: Time) -> VfsResult<()> {
        Err(VfsError::from(VfsErrorKind::NotSupported))
    }
    /// Returns true if a file or directory at path exists, false otherwise
    async fn exists(&self, path: &str) -> VfsResult<bool>;

    /// Removes the file at this path
    async fn remove_file(&self, path: &str) -> VfsResult<()>;

    /// Removes the directory at this path
    async fn remove_dir(&self, path: &str) -> VfsResult<()>;

    /// Copies the src path to the destination path within the same filesystem (optional)
    async fn copy_file(&self, _src: &str, _dest: &str) -> VfsResult<()> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// Moves the src path to the destination path within the same filesystem (optional)
    async fn move_file(&self, _src: &str, _dest: &str) -> VfsResult<()> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// Moves the src directory to the destination path within the same filesystem (optional)
    async fn move_dir(&self, _src: &str, _dest: &str) -> VfsResult<()> {
        Err(VfsErrorKind::NotSupported.into())
    }
}
