//! Error and Result definitions

use super::super::error::{Error, IoError};
use alloc::{
    boxed::Box,
    string::{String, ToString},
};
use core::fmt;

/// The error type of this crate
#[derive(Debug)]
pub struct VfsError<E> {
    /// The path this error was encountered in
    path: String,
    /// The kind of error
    pub kind: VfsErrorKind<E>,
    /// An optional human-readable string describing the context for this error
    ///
    /// If not provided, a generic context message is used
    context: String,
    /// The underlying error
    cause: Option<Box<VfsError<E>>>,
}

impl<E> embedded_io_async::Error for VfsError<E>
where
    E: embedded_io_async::Error + fmt::Debug + 'static, // VfsError がラップするエラーも `embedded_io_async::Error` を実装し、Debug 可能である必要がある
{
    fn kind(&self) -> embedded_io_async::ErrorKind {
        // VfsErrorKind に応じて適切な ErrorKind を返す
        match self.kind {
            VfsErrorKind::FileNotFound => embedded_io_async::ErrorKind::NotFound,
            _ => embedded_io_async::ErrorKind::Unsupported,
        }
    }
}

/// The only way to create a VfsError is via a VfsErrorKind
///
/// This conversion implements certain normalizations
impl<E> From<VfsErrorKind<E>> for VfsError<E> {
    fn from(kind: VfsErrorKind<E>) -> Self {
        Self {
            path: "PATH NOT FILLED BY VFS LAYER".into(),
            kind,
            context: "An error occured".into(),
            cause: None,
        }
    }
}

impl<E: IoError> From<Error<E>> for VfsError<E> {
    fn from(err: Error<E>) -> Self {
        let kind = err.into();
        Self {
            path: "PATH NOT FILLED BY VFS LAYER".into(),
            kind,
            context: "An error occurred".into(),
            cause: None,
        }
    }
}

impl<E> From<Error<E>> for VfsErrorKind<E> {
    fn from(err: Error<E>) -> Self {
        match err {
            Error::Io(io_error_t) => VfsErrorKind::IoError(io_error_t),
            _ => VfsErrorKind::Other("Generic error from fatfs.".to_string()),
        }
    }
}

//impl<E: IoError> From<E> for VfsErrorKind<E> {
//fn from(err: E) -> Self {
//VfsErrorKind::IoError(err)
//}
//}

impl<E: IoError> VfsError<E> {
    // Path filled by the VFS crate rather than the implementations
    pub fn with_path(mut self, path: impl Into<String>) -> Self {
        self.path = path.into();
        self
    }

    pub fn with_context<C, F>(mut self, context: F) -> Self
    where
        C: fmt::Display + Send + Sync + 'static,
        F: FnOnce() -> C,
    {
        self.context = context().to_string();
        self
    }

    pub fn with_cause(mut self, cause: VfsError<E>) -> Self {
        self.cause = Some(Box::new(cause));
        self
    }

    pub fn kind(&self) -> &VfsErrorKind<E> {
        &self.kind
    }

    pub fn path(&self) -> &String {
        &self.path
    }
}

impl<E: fmt::Display + IoError> fmt::Display for VfsError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} for '{}': {}", self.context, self.path, self.kind())
    }
}

/// The kinds of errors that can occur
#[derive(Debug)]
pub enum VfsErrorKind<E> {
    /// A generic I/O error
    ///
    /// Certain standard I/O errors are normalized to their VfsErrorKind counterparts
    IoError(E),

    /// A generic async I/O error
    AsyncIoError(E),

    /// The file or directory at the given path could not be found
    FileNotFound,

    /// The given path is invalid, e.g. because contains '.' or '..'
    InvalidPath,

    /// Generic error variant
    Other(String),

    /// There is already a directory at the given path
    DirectoryExists,

    /// There is already a file at the given path
    FileExists,

    /// Functionality not supported by this filesystem
    NotSupported,
}

impl<E: fmt::Display> fmt::Display for VfsErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VfsErrorKind::IoError(cause) => {
                write!(f, "IO error: {cause}")
            }
            VfsErrorKind::AsyncIoError(cause) => {
                write!(f, "Async IO error: {cause}")
            }
            VfsErrorKind::FileNotFound => {
                write!(f, "The file or directory could not be found")
            }
            VfsErrorKind::InvalidPath => {
                write!(f, "The path is invalid")
            }
            VfsErrorKind::Other(message) => {
                write!(f, "FileSystem error: {message}")
            }
            VfsErrorKind::NotSupported => {
                write!(f, "Functionality not supported by this filesystem")
            }
            VfsErrorKind::DirectoryExists => {
                write!(f, "Directory already exists")
            }
            VfsErrorKind::FileExists => {
                write!(f, "File already exists")
            }
        }
    }
}

/// The result type of this crate
pub type VfsResult<T, E> = core::result::Result<T, VfsError<E>>;

impl<E: IoError> IoError for VfsError<E> {
    fn is_interrupted(&self) -> bool {
        todo!();
    }
    fn new_unexpected_eof_error() -> Self {
        todo!();
    }
    fn new_write_zero_error() -> Self {
        todo!();
    }
    fn other_error() -> Self {
        todo!();
    }
}
