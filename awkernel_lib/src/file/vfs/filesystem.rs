//! The filesystem trait definitions needed to implement new virtual filesystems

use super::super::error::IoError;
use super::error::VfsErrorKind;
use super::{
    error::VfsError, error::VfsResult, path::SeekAndRead, path::SeekAndWrite, path::VfsMetadata,
    path::VfsPath,
};
use crate::time::Time;
use alloc::{boxed::Box, string::String};
use core::fmt::Debug;

/// File system implementations must implement this trait
/// All path parameters are absolute, starting with '/', except for the root directory
/// which is simply the empty string (i.e. "")
/// The character '/' is used to delimit directories on all platforms.
/// Path components may be any UTF-8 string, except "/", "." and ".."
///
/// Please use the test_macros [test_macros::test_vfs!] and [test_macros::test_vfs_readonly!]
pub trait FileSystem: Debug + Sync + Send + 'static {
    type Error: IoError + Clone;
    /// Iterates over all direct children of this directory path
    /// NOTE: the returned String items denote the local bare filenames, i.e. they should not contain "/" anywhere
    fn read_dir(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn Iterator<Item = String> + Send>, Self::Error>;
    /// Creates the directory at this path
    ///
    /// Note that the parent directory must already exist.
    fn create_dir(&self, path: &str) -> VfsResult<(), Self::Error>;
    /// Opens the file at this path for reading
    #[allow(clippy::type_complexity)]
    fn open_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn SeekAndRead<Error = VfsError<Self::Error>> + Send>, Self::Error>;
    /// Creates a file at this path for writing
    #[allow(clippy::type_complexity)]
    fn create_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn SeekAndWrite<Error = VfsError<Self::Error>> + Send>, Self::Error>;
    /// Opens the file at this path for appending
    #[allow(clippy::type_complexity)]
    fn append_file(
        &self,
        path: &str,
    ) -> VfsResult<Box<dyn SeekAndWrite<Error = VfsError<Self::Error>> + Send>, Self::Error>;
    /// Returns the file metadata for the file at this path
    fn metadata(&self, path: &str) -> VfsResult<VfsMetadata, Self::Error>;
    /// Sets the files creation timestamp, if the implementation supports it
    fn set_creation_time(&self, _path: &str, _time: Time) -> VfsResult<(), Self::Error> {
        Err(VfsError::from(VfsErrorKind::NotSupported))
    }
    /// Sets the files modification timestamp, if the implementation supports it
    fn set_modification_time(&self, _path: &str, _time: Time) -> VfsResult<(), Self::Error> {
        Err(VfsError::from(VfsErrorKind::NotSupported))
    }
    /// Sets the files access timestamp, if the implementation supports it
    fn set_access_time(&self, _path: &str, _time: Time) -> VfsResult<(), Self::Error> {
        Err(VfsError::from(VfsErrorKind::NotSupported))
    }
    /// Returns true if a file or directory at path exists, false otherwise
    fn exists(&self, path: &str) -> VfsResult<bool, Self::Error>;
    /// Removes the file at this path
    fn remove_file(&self, path: &str) -> VfsResult<(), Self::Error>;
    /// Removes the directory at this path
    fn remove_dir(&self, path: &str) -> VfsResult<(), Self::Error>;
    /// Copies the src path to the destination path within the same filesystem (optional)
    fn copy_file(&self, _src: &str, _dest: &str) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// Moves the src path to the destination path within the same filesystem (optional)
    fn move_file(&self, _src: &str, _dest: &str) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
    /// Moves the src directory to the destination path within the same filesystem (optional)
    fn move_dir(&self, _src: &str, _dest: &str) -> VfsResult<(), Self::Error> {
        Err(VfsErrorKind::NotSupported.into())
    }
}

impl<T: FileSystem> From<T> for VfsPath<T::Error> {
    fn from(filesystem: T) -> Self {
        VfsPath::new(filesystem)
    }
}
