//! Error and Result definitions
use alloc::{
    boxed::Box,
    string::{String, ToString},
};
use core::fmt;

/// The error type of this crate
#[derive(Debug)]
pub struct VfsError {
    /// The path this error was encountered in
    path: String,
    /// The kind of error
    kind: VfsErrorKind,
    /// An optional human-readable string describing the context for this error
    ///
    /// If not provided, a generic context message is used
    context: String,
    /// The underlying error
    cause: Option<Box<VfsError>>,
}

/// The only way to create a VfsError is via a VfsErrorKind
///
/// This conversion implements certain normalizations
impl From<VfsErrorKind> for VfsError {
    fn from(kind: VfsErrorKind) -> Self {
        Self {
            path: "PATH NOT FILLED BY VFS LAYER".into(),
            kind,
            context: "An error occured".into(),
            cause: None,
        }
    }
}

impl VfsError {
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

    pub fn with_cause(mut self, cause: VfsError) -> Self {
        self.cause = Some(Box::new(cause));
        self
    }

    pub fn kind(&self) -> &VfsErrorKind {
        &self.kind
    }

    pub fn path(&self) -> &String {
        &self.path
    }
}

impl fmt::Display for VfsError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} for '{}': {}", self.context, self.path, self.kind())
    }
}

/// The kinds of errors that can occur
#[derive(Debug)]
pub enum VfsErrorKind {
    /// A generic I/O error
    ///
    /// Certain standard I/O errors are normalized to their VfsErrorKind counterparts
    IoError(VfsIoError),

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

impl fmt::Display for VfsErrorKind {
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

#[derive(Debug)]
pub enum VfsIoError {
    OutOfBounds,
    WriteZero,
    UnexpectedEof,
    Interrupted,
    Other(String),
}

impl fmt::Display for VfsIoError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VfsIoError::OutOfBounds => {
                write!(f, "Out of bounds access")
            }
            VfsIoError::WriteZero => {
                write!(f, "Failed to write whole buffer")
            }
            VfsIoError::UnexpectedEof => {
                write!(f, "Failed to fill whole buffer")
            }
            VfsIoError::Interrupted => {
                write!(f, "Operation interrupted")
            }
            VfsIoError::Other(msg) => {
                write!(f, "An error occured: {msg}")
            }
        }
    }
}

/// The result type of this crate
pub type VfsResult<T> = core::result::Result<T, VfsError>;

impl From<crate::file::block_device::BlockDeviceAdapterError> for VfsIoError {
    fn from(e: crate::file::block_device::BlockDeviceAdapterError) -> Self {
        use crate::file::block_device::BlockDeviceAdapterError;
        match e {
            BlockDeviceAdapterError::OutOfBounds => VfsIoError::OutOfBounds,
            BlockDeviceAdapterError::IoError => VfsIoError::Other("Block device I/O error".into()),
            BlockDeviceAdapterError::ReadOnly => VfsIoError::Other("Device is read-only".into()),
            BlockDeviceAdapterError::WriteZero => VfsIoError::WriteZero,
            BlockDeviceAdapterError::UnexpectedEof => VfsIoError::UnexpectedEof,
            BlockDeviceAdapterError::Interrupted => VfsIoError::Interrupted,
            BlockDeviceAdapterError::DeviceBusy => VfsIoError::Other("Device is busy".into()),
            BlockDeviceAdapterError::Other(msg) => VfsIoError::Other(msg),
        }
    }
}
