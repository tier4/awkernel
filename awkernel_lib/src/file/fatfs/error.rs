use super::super::error::IoError;
use super::super::vfs::error::VfsErrorKind;
use alloc::string::ToString;

/// Error enum with all errors that can be returned by functions from this crate
///
/// Generic parameter `T` is a type of external error returned by the user provided storage
#[derive(Debug, Clone)]
#[non_exhaustive]
pub enum Error<T> {
    /// A user provided storage instance returned an error during an input/output operation.
    Io(T),
    /// A read operation cannot be completed because an end of a file has been reached prematurely.
    UnexpectedEof,
    /// A write operation cannot be completed because `Write::write` returned 0.
    WriteZero,
    /// A parameter was incorrect.
    InvalidInput,
    /// A requested file or directory has not been found.
    NotFound,
    /// A file or a directory with the same name already exists.
    AlreadyExists,
    /// An operation cannot be finished because a directory is not empty.
    DirectoryIsNotEmpty,
    /// File system internal structures are corrupted/invalid.
    CorruptedFileSystem,
    /// There is not enough free space on the storage to finish the requested operation.
    NotEnoughSpace,
    /// The provided file name is either too long or empty.
    InvalidFileNameLength,
    /// The provided file name contains an invalid character.
    UnsupportedFileNameCharacter,
}

impl<E: IoError> From<Error<E>> for VfsErrorKind<E> {
    fn from(err: Error<E>) -> Self {
        match err {
            Error::Io(io_error_t) => VfsErrorKind::IoError(io_error_t),
            _ => VfsErrorKind::Other("Generic error from fatfs.".to_string()),
        }
    }
}

impl<T: core::fmt::Display> core::fmt::Display for Error<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        match self {
            Error::Io(io_error) => write!(f, "IO error: {io_error}"),
            Error::UnexpectedEof => write!(f, "Unexpected end of file"),
            Error::NotEnoughSpace => write!(f, "Not enough space"),
            Error::WriteZero => write!(f, "Write zero"),
            Error::InvalidInput => write!(f, "Invalid input"),
            Error::InvalidFileNameLength => write!(f, "Invalid file name length"),
            Error::UnsupportedFileNameCharacter => {
                write!(f, "Unsupported file name character")
            }
            Error::DirectoryIsNotEmpty => write!(f, "Directory is not empty"),
            Error::NotFound => write!(f, "No such file or directory"),
            Error::AlreadyExists => write!(f, "File or directory already exists"),
            Error::CorruptedFileSystem => write!(f, "Corrupted file system"),
        }
    }
}

impl<T: core::fmt::Debug + IoError> IoError for Error<T> {
    fn is_interrupted(&self) -> bool {
        match self {
            Error::<T>::Io(io_error) => io_error.is_interrupted(),
            _ => false,
        }
    }

    fn new_unexpected_eof_error() -> Self {
        Error::<T>::UnexpectedEof
    }

    fn new_write_zero_error() -> Self {
        Error::<T>::WriteZero
    }
}

impl<T: IoError> From<T> for Error<T> {
    fn from(error: T) -> Self {
        Error::Io(error)
    }
}
