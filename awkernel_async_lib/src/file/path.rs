//! Virtual filesystem path (async version)
//!
//! The virtual file system abstraction generalizes over file systems and allow using
//! different VirtualFileSystem implementations (i.e. an in memory implementation for unit tests)

use crate::file::fatfs::AsyncFatFs;

use super::filesystem::{AsyncFileSystem, AsyncSeekAndRead, AsyncSeekAndWrite};
use awkernel_lib::{
    console,
    file::{
        error::IoError,
        memfs::InMemoryDiskError,
        vfs::{
            error::{VfsError, VfsErrorKind, VfsResult},
            path::{PathLike, VfsFileType, VfsMetadata},
        },
    },
    time::Time,
};

use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    sync::Arc,
    vec,
    vec::Vec,
};
use async_recursion::async_recursion;
use core::{
    pin::Pin,
    task::{Context, Poll},
};
use futures::{future::BoxFuture, FutureExt, Stream, StreamExt};

struct AsyncVFS<E: IoError> {
    fs: Box<dyn AsyncFileSystem<Error = E>>,
}

/// A virtual filesystem path, identifying a single file or directory in this virtual filesystem
#[derive(Clone)]
pub struct AsyncVfsPath<E: IoError> {
    path: String,
    fs: Arc<AsyncVFS<E>>,
}

impl<E: IoError + Clone> PathLike for AsyncVfsPath<E> {
    type Error = E;
    fn get_path(&self) -> String {
        self.path.clone()
    }
}

impl<E: IoError> PartialEq for AsyncVfsPath<E> {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path && Arc::ptr_eq(&self.fs, &other.fs)
    }
}

impl<E: IoError> Eq for AsyncVfsPath<E> {}

impl AsyncVfsPath<InMemoryDiskError> {
    pub fn new_in_memory_fatfs() -> Self {
        let fs = AsyncFatFs::new_in_memory();
        AsyncVfsPath::from(fs)
    }
}

impl<E: IoError + Clone + Send + Sync + 'static> AsyncVfsPath<E> {
    /// Creates a root path for the given filesystem
    pub fn new<T: AsyncFileSystem<Error = E>>(filesystem: T) -> Self {
        AsyncVfsPath {
            path: "".to_string(),
            fs: Arc::new(AsyncVFS {
                fs: Box::new(filesystem),
            }),
        }
    }

    /// Returns the string representation of this path
    pub fn as_str(&self) -> &str {
        &self.path
    }

    /// Appends a path segment to this path, returning the result
    pub fn join(&self, path: impl AsRef<str>) -> VfsResult<Self, E> {
        let new_path = self.join_internal(&self.path, path.as_ref())?;
        Ok(Self {
            path: new_path,
            fs: self.fs.clone(),
        })
    }

    /// Returns the root path of this filesystem
    pub fn root(&self) -> Self {
        AsyncVfsPath {
            path: "".to_string(),
            fs: self.fs.clone(),
        }
    }

    /// Returns true if this is the root path
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }

    /// Creates the directory at this path
    pub async fn create_dir(&self) -> VfsResult<(), E> {
        self.get_parent("create directory").await?;
        self.fs.fs.create_dir(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not create directory")
        })
    }

    /// Creates the directory at this path, also creating parent directories as necessary
    pub async fn create_dir_all(&self) -> VfsResult<(), E> {
        let mut pos = 1;
        let path = &self.path;
        if path.is_empty() {
            // root exists always
            return Ok(());
        }
        loop {
            // Iterate over path segments
            let end = path[pos..]
                .find('/')
                .map(|it| it + pos)
                .unwrap_or_else(|| path.len());
            let directory = &path[..end];
            if let Err(error) = self.fs.fs.create_dir(directory).await {
                match error.kind() {
                    VfsErrorKind::DirectoryExists => {}
                    _ => {
                        return Err(error
                            .with_path(directory)
                            .with_context(|| format!("Could not create directories at '{path}'")))
                    }
                }
            }
            if end == path.len() {
                break;
            }
            pos = end + 1;
        }
        Ok(())
    }

    /// Iterates over all entries of this directory path
    pub async fn read_dir(
        &self,
    ) -> VfsResult<Box<dyn Unpin + Stream<Item = AsyncVfsPath<E>> + Send>, E> {
        let parent = self.path.clone();
        let fs = self.fs.clone();
        Ok(Box::new(
            self.fs
                .fs
                .read_dir(&self.path)
                .await
                .map_err(|err| {
                    err.with_path(&self.path)
                        .with_context(|| "Could not read directory")
                })?
                .map(move |path| {
                    console::print(path.as_str());
                    AsyncVfsPath {
                        path: format!("{}/{}", parent, path),
                        fs: fs.clone(),
                    }
                }),
        ))
    }

    /// Creates a file at this path for writing, overwriting any existing file
    pub async fn create_file(&self) -> VfsResult<Box<dyn AsyncSeekAndWrite<E> + Send + Unpin>, E> {
        self.get_parent("create file").await?;
        self.fs.fs.create_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not create file")
        })
    }

    /// Opens the file at this path for reading
    pub async fn open_file(&self) -> VfsResult<Box<dyn AsyncSeekAndRead<E> + Send + Unpin>, E> {
        self.fs.fs.open_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not open file")
        })
    }

    /// Checks whether parent is a directory
    async fn get_parent(&self, action: &str) -> VfsResult<(), E> {
        let parent = self.parent();
        if !parent.exists().await? {
            return Err(VfsError::from(VfsErrorKind::Other(format!(
                "Could not {action}, parent directory does not exist"
            )))
            .with_path(&self.path));
        }
        let metadata = parent.metadata().await?;
        if metadata.file_type != VfsFileType::Directory {
            return Err(VfsError::from(VfsErrorKind::Other(format!(
                "Could not {action}, parent path is not a directory"
            )))
            .with_path(&self.path));
        }
        Ok(())
    }

    /// Opens the file at this path for appending
    pub async fn append_file(&self) -> VfsResult<Box<dyn AsyncSeekAndWrite<E> + Send + Unpin>, E> {
        self.fs.fs.append_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not open file for appending")
        })
    }

    /// Removes the file at this path
    pub async fn remove_file(&self) -> VfsResult<(), E> {
        self.fs.fs.remove_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not remove file")
        })
    }

    /// Removes the directory at this path
    pub async fn remove_dir(&self) -> VfsResult<(), E> {
        self.fs.fs.remove_dir(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not remove directory")
        })
    }

    /// Ensures that the directory at this path is removed, recursively deleting all contents if necessary
    #[async_recursion]
    pub async fn remove_dir_all(&self) -> VfsResult<(), E> {
        if !self.exists().await? {
            return Ok(());
        }
        let mut path_stream = self.read_dir().await?;
        while let Some(child) = path_stream.next().await {
            let metadata = child.metadata().await?;
            match metadata.file_type {
                VfsFileType::File => child.remove_file().await?,
                VfsFileType::Directory => child.remove_dir_all().await?,
            }
        }
        self.remove_dir().await?;
        Ok(())
    }

    /// Returns the file metadata for the file at this path
    pub async fn metadata(&self) -> VfsResult<VfsMetadata, E> {
        self.fs.fs.metadata(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not get metadata")
        })
    }

    /// Sets the files creation timestamp at this path
    pub async fn set_creation_time(&self, time: Time) -> VfsResult<(), E> {
        self.fs
            .fs
            .set_creation_time(&self.path, time)
            .await
            .map_err(|err| {
                err.with_path(&self.path)
                    .with_context(|| "Could not set creation timestamp.")
            })
    }

    /// Sets the files modification timestamp at this path
    pub async fn set_modification_time(&self, time: Time) -> VfsResult<(), E> {
        self.fs
            .fs
            .set_modification_time(&self.path, time)
            .await
            .map_err(|err| {
                err.with_path(&self.path)
                    .with_context(|| "Could not set modification timestamp.")
            })
    }

    /// Sets the files access timestamp at this path
    pub async fn set_access_time(&self, time: Time) -> VfsResult<(), E> {
        self.fs
            .fs
            .set_access_time(&self.path, time)
            .await
            .map_err(|err| {
                err.with_path(&self.path)
                    .with_context(|| "Could not set access timestamp.")
            })
    }

    /// Returns `true` if the path exists and is pointing at a regular file, otherwise returns `false`.
    pub async fn is_file(&self) -> VfsResult<bool, E> {
        if !self.exists().await? {
            return Ok(false);
        }
        let metadata = self.metadata().await?;
        Ok(metadata.file_type == VfsFileType::File)
    }

    /// Returns `true` if the path exists and is pointing at a directory, otherwise returns `false`.
    pub async fn is_dir(&self) -> VfsResult<bool, E> {
        if !self.exists().await? {
            return Ok(false);
        }
        let metadata = self.metadata().await?;
        Ok(metadata.file_type == VfsFileType::Directory)
    }

    /// Returns true if a file or directory exists at this path, false otherwise
    pub async fn exists(&self) -> VfsResult<bool, E> {
        self.fs.fs.exists(&self.path).await
    }

    /// Returns the filename portion of this path
    pub fn filename(&self) -> String {
        self.filename_internal()
    }

    /// Returns the extension portion of this path
    pub fn extension(&self) -> Option<String> {
        self.extension_internal()
    }

    /// Returns the parent path of this portion of this path
    pub fn parent(&self) -> Self {
        let parent_path = self.parent_internal(&self.path);
        Self {
            path: parent_path,
            fs: self.fs.clone(),
        }
    }

    /// Reads a complete file to a string
    pub async fn read_to_string(&self) -> VfsResult<String, E> {
        let metadata = self.metadata().await?;
        if metadata.file_type != VfsFileType::File {
            return Err(
                VfsError::from(VfsErrorKind::Other("Path is a directory".into()))
                    .with_path(&self.path)
                    .with_context(|| "Could not read path"),
            );
        }
        let mut buffer = vec![0; metadata.len as usize];
        self.open_file()
            .await?
            .read_exact(&mut buffer)
            .await
            .map_err(|err| {
                err.with_path(&self.path)
                    .with_context(|| "Could not read path")
            })?;

        String::from_utf8(buffer).map_err(|_| {
            VfsError::from(VfsErrorKind::Other("Invalid UTF-8 sequence".into()))
                .with_path(&self.path)
                .with_context(|| "Could not read path as string")
        })
    }
}
