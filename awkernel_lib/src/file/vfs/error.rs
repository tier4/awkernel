//! Error and Result definitions

use super::super::error::IoError;
use super::super::fatfs::error::Error as FatfsError;
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
    kind: VfsErrorKind<E>,
    /// An optional human-readable string describing the context for this error
    ///
    /// If not provided, a generic context message is used
    context: String,
    /// The underlying error
    cause: Option<Box<VfsError<E>>>,
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

    /// The file or directory at the given path could not be found
    NotFound,

    /// The given path is invalid, e.g. because contains '.' or '..'
    InvalidPath,

    /// Generic error variant
    Other(String),

    /// There is already a file or a directory at the given path
    AlreadyExists,

    /// An operation cannot be finished because a directory is not empty.
    DirectoryIsNotEmpty,

    /// File system internal structures are corrupted/invalid.
    CorruptedFileSystem,

    /// There is not enough free space on the storage to finish the requested operation.
    NotEnoughSpace,

    /// Functionality not supported by this filesystem
    NotSupported,
}

impl<E: fmt::Display> fmt::Display for VfsErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VfsErrorKind::IoError(cause) => {
                write!(f, "IO error: {cause}")
            }
            VfsErrorKind::NotFound => {
                write!(f, "The file or directory could not be found")
            }
            VfsErrorKind::InvalidPath => {
                write!(f, "The path is invalid")
            }
            VfsErrorKind::Other(message) => {
                write!(f, "FileSystem error: {message}")
            }
            VfsErrorKind::AlreadyExists => {
                write!(f, "File or directory already exists")
            }
            VfsErrorKind::DirectoryIsNotEmpty => {
                write!(f, "Directory is not empty")
            }
            VfsErrorKind::CorruptedFileSystem => {
                write!(f, "Corrupted file system")
            }
            VfsErrorKind::NotEnoughSpace => {
                write!(f, "Not enough space")
            }
            VfsErrorKind::NotSupported => {
                write!(f, "Functionality not supported by this filesystem")
            }
        }
    }
}

/// The result type of this crate
pub type VfsResult<T, E> = core::result::Result<T, VfsError<E>>;
