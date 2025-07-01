//! Error and Result definitions

use super::super::error::IoError;
use alloc::{
    boxed::Box,
    string::{String, ToString},
};
use core::fmt;

/// The error type of this crate
#[derive(Debug)]
pub struct VfsError<E: IoError> {
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
impl<E: IoError> From<VfsErrorKind<E>> for VfsError<E> {
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
pub enum VfsErrorKind<E: IoError> {
    /// A generic I/O error
    ///
    /// Certain standard I/O errors are normalized to their VfsErrorKind counterparts
    IoError(E),

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

impl<E: fmt::Display + IoError> fmt::Display for VfsErrorKind<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VfsErrorKind::IoError(cause) => {
                write!(f, "IO error: {cause}")
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
