//! Virtual filesystem path (async version)
//!
//! The virtual file system abstraction generalizes over file systems and allow using
//! different VirtualFileSystem implementations (i.e. an in memory implementation for unit tests)

use crate::file::fatfs::AsyncFatFs;

use super::filesystem::{AsyncFileSystem, AsyncSeekAndRead, AsyncSeekAndWrite};
use awkernel_lib::{
    console,
    file::vfs::{
        error::{VfsError, VfsErrorKind, VfsResult},
        path::{PathLike, VfsFileType, VfsMetadata},
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

struct AsyncVFS {
    fs: Box<dyn AsyncFileSystem>,
}

/// A virtual filesystem path, identifying a single file or directory in this virtual filesystem
#[derive(Clone)]
pub struct AsyncVfsPath {
    path: String,
    fs: Arc<AsyncVFS>,
}

impl PathLike for AsyncVfsPath {
    fn get_path(&self) -> String {
        self.path.clone()
    }
}

impl PartialEq for AsyncVfsPath {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path && Arc::ptr_eq(&self.fs, &other.fs)
    }
}

impl Eq for AsyncVfsPath {}

impl AsyncVfsPath {
    pub fn new_in_memory_fatfs() -> Self {
        let fs = AsyncFatFs::new_in_memory();
        AsyncVfsPath::from(Box::new(fs) as Box<dyn AsyncFileSystem>)
    }
}

impl AsyncVfsPath {
    /// Creates a root path for the given filesystem
    pub fn new(filesystem: Box<dyn AsyncFileSystem + Send + Sync>) -> Self {
        AsyncVfsPath {
            path: "".to_string(),
            fs: Arc::new(AsyncVFS { fs: filesystem }),
        }
    }

    /// Returns the string representation of this path
    pub fn as_str(&self) -> &str {
        &self.path
    }

    /// Appends a path segment to this path, returning the result
    pub fn join(&self, path: impl AsRef<str>) -> VfsResult<Self> {
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
    pub async fn create_dir(&self) -> VfsResult<()> {
        self.get_parent("create directory").await?;
        self.fs.fs.create_dir(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not create directory")
        })
    }

    /// Creates the directory at this path, also creating parent directories as necessary
    pub async fn create_dir_all(&self) -> VfsResult<()> {
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
                    VfsErrorKind::AlreadyExists => {}
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
    pub async fn read_dir(&self) -> VfsResult<Box<dyn Unpin + Stream<Item = AsyncVfsPath> + Send>> {
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
                        path: format!("{parent}/{path}"),
                        fs: fs.clone(),
                    }
                }),
        ))
    }

    /// Creates a file at this path for writing, overwriting any existing file
    pub async fn create_file(&self) -> VfsResult<Box<dyn AsyncSeekAndWrite + Send + Unpin>> {
        self.get_parent("create file").await?;
        self.fs.fs.create_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not create file")
        })
    }

    /// Opens the file at this path for reading
    pub async fn open_file(&self) -> VfsResult<Box<dyn AsyncSeekAndRead + Send + Unpin>> {
        self.fs.fs.open_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not open file")
        })
    }

    /// Checks whether parent is a directory
    async fn get_parent(&self, action: &str) -> VfsResult<()> {
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
    pub async fn append_file(&self) -> VfsResult<Box<dyn AsyncSeekAndWrite + Send + Unpin>> {
        self.fs.fs.append_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not open file for appending")
        })
    }

    /// Removes the file at this path
    pub async fn remove_file(&self) -> VfsResult<()> {
        self.fs.fs.remove_file(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not remove file")
        })
    }

    /// Removes the directory at this path
    pub async fn remove_dir(&self) -> VfsResult<()> {
        self.fs.fs.remove_dir(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not remove directory")
        })
    }

    /// Ensures that the directory at this path is removed, recursively deleting all contents if necessary
    #[async_recursion]
    pub async fn remove_dir_all(&self) -> VfsResult<()> {
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
    pub async fn metadata(&self) -> VfsResult<VfsMetadata> {
        self.fs.fs.metadata(&self.path).await.map_err(|err| {
            err.with_path(&self.path)
                .with_context(|| "Could not get metadata")
        })
    }

    /// Sets the files creation timestamp at this path
    pub async fn set_creation_time(&self, time: Time) -> VfsResult<()> {
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
    pub async fn set_modification_time(&self, time: Time) -> VfsResult<()> {
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
    pub async fn set_access_time(&self, time: Time) -> VfsResult<()> {
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
    pub async fn is_file(&self) -> VfsResult<bool> {
        if !self.exists().await? {
            return Ok(false);
        }
        let metadata = self.metadata().await?;
        Ok(metadata.file_type == VfsFileType::File)
    }

    /// Returns `true` if the path exists and is pointing at a directory, otherwise returns `false`.
    pub async fn is_dir(&self) -> VfsResult<bool> {
        if !self.exists().await? {
            return Ok(false);
        }
        let metadata = self.metadata().await?;
        Ok(metadata.file_type == VfsFileType::Directory)
    }

    /// Returns true if a file or directory exists at this path, false otherwise
    pub async fn exists(&self) -> VfsResult<bool> {
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

    /// Recursively iterates over all the directories and files at this path
    pub async fn walk_dir(&self) -> VfsResult<WalkDirIterator> {
        Ok(WalkDirIterator {
            inner: self.read_dir().await?,
            todo: vec![],
            prev_result: None,
            metadata_fut: None,
            read_dir_fut: None,
        })
    }

    /// Reads a complete file to a string
    pub async fn read_to_string(&self) -> VfsResult<String> {
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

    /// Copies a file to a new destination
    pub async fn copy_file(&self, destination: &AsyncVfsPath) -> VfsResult<()> {
        async {
            if destination.exists().await? {
                return Err(
                    VfsError::from(VfsErrorKind::Other("Destination exists already".into()))
                        .with_path(&self.path),
                );
            }
            if Arc::ptr_eq(&self.fs, &destination.fs) {
                let result = self.fs.fs.copy_file(&self.path, &destination.path).await;
                if !matches!(result, Err(ref err) if matches!(err.kind(), VfsErrorKind::NotSupported))
                {
                    return result;
                }
            }
            let mut src = self.open_file().await?;
            let mut dest = destination.create_file().await?;
            simple_async_copy(&mut src, &mut dest).await.map_err(|err| match err {
                CopyError::ReadError(e) => e,
                CopyError::WriteError(e) => e,
            })?;
            Ok(())
        }
        .await
        .map_err(|err| {
            err.with_path(&self.path).with_context(|| {
                format!("Could not copy '{}' to '{}'", self.as_str(), destination.as_str())
            })
        })
    }

    /// Moves or renames a file to a new destination
    pub async fn move_file(&self, destination: &AsyncVfsPath) -> VfsResult<()> {
        async {
            if destination.exists().await? {
                return Err(VfsError::from(VfsErrorKind::Other(
                    "Destination exists already".into(),
                ))
                .with_path(&destination.path));
            }
            if Arc::ptr_eq(&self.fs, &destination.fs) {
                let result = self.fs.fs.move_file(&self.path, &destination.path).await;
                if !matches!(result, Err(ref err) if matches!(err.kind(), VfsErrorKind::NotSupported))
                {
                    return result;
                }
            }
            let mut src = self.open_file().await?;
            let mut dest = destination.create_file().await?;
            simple_async_copy(&mut src, &mut dest).await.map_err(|err| match err {
                CopyError::ReadError(e) => e,
                CopyError::WriteError(e) => e,
            })?;
            self.remove_file().await?;
            Ok(())
        }
        .await
        .map_err(|err| {
            err.with_path(&self.path).with_context(|| {
                format!("Could not move '{}' to '{}'", self.as_str(), destination.as_str())
            })
        })
    }

    /// Copies a directory to a new destination, recursively
    pub async fn copy_dir(&self, destination: &AsyncVfsPath) -> VfsResult<u64> {
        let files_copied = async {
            let mut files_copied = 0u64;
            if destination.exists().await? {
                return Err(VfsError::from(VfsErrorKind::Other(
                    "Destination exists already".into(),
                ))
                .with_path(&destination.path));
            }
            destination.create_dir().await?;
            let prefix = &self.path;
            let prefix_len = prefix.len();
            let mut path_stream = self.walk_dir().await?;
            while let Some(result) = path_stream.next().await {
                let src_path = result?;
                let dest_path = destination.join(&src_path.as_str()[prefix_len + 1..])?;
                match src_path.metadata().await?.file_type {
                    VfsFileType::Directory => dest_path.create_dir().await?,
                    VfsFileType::File => {
                        src_path.copy_file(&dest_path).await?;
                        files_copied += 1;
                    }
                }
            }
            Ok(files_copied)
        }
        .await
        .map_err(|err: VfsError| {
            err.with_path(&self.path).with_context(|| {
                format!(
                    "Could not copy directory '{}' to '{}'",
                    self.as_str(),
                    destination.as_str()
                )
            })
        })?;
        Ok(files_copied)
    }

    /// Moves a directory to a new destination, including subdirectories and files
    pub async fn move_dir(&self, destination: &AsyncVfsPath) -> VfsResult<()> {
        async {
            if destination.exists().await? {
                return Err(
                    VfsError::from(VfsErrorKind::Other("Destination exists already".into()))
                        .with_path(&destination.path),
                );
            }
            if Arc::ptr_eq(&self.fs, &destination.fs) {
                let result = self.fs.fs.move_dir(&self.path, &destination.path).await;
                if !matches!(result, Err(ref err) if matches!(err.kind(), VfsErrorKind::NotSupported))
                {
                    return result;
                }
            }
            destination.create_dir().await?;
            let prefix = &self.path;
            let prefix_len = prefix.len();
            let mut path_stream = self.walk_dir().await?;
            while let Some(result) = path_stream.next().await {
                let src_path = result?;
                let dest_path = destination.join(&src_path.as_str()[prefix_len + 1..])?;
                match src_path.metadata().await?.file_type {
                    VfsFileType::Directory => dest_path.create_dir().await?,
                    VfsFileType::File => src_path.move_file(&dest_path).await?,
                }
            }
            self.remove_dir_all().await?;
            Ok(())
        }
        .await
        .map_err(|err: VfsError| {
            err.with_path(&self.path).with_context(|| {
                format!(
                    "Could not move directory '{}' to '{}'",
                    self.as_str(),
                    destination.as_str()
                )
            })
        })
    }
}

type ReadDirOperationResult =
    Result<Box<(dyn Stream<Item = AsyncVfsPath> + Send + Unpin)>, VfsError>;

/// An iterator for recursively walking a file hierarchy
pub struct WalkDirIterator {
    /// the path iterator of the current directory
    inner: Box<dyn Stream<Item = AsyncVfsPath> + Send + Unpin>,
    /// stack of subdirectories still to walk
    todo: Vec<AsyncVfsPath>,
    /// used to store the previous yield of the todo stream,
    /// which would otherwise get dropped if path.metadata() is pending
    prev_result: Option<AsyncVfsPath>,
    // Used to store futures when poll_next returns pending
    // this ensures a new future is not spawned on each poll.
    read_dir_fut: Option<BoxFuture<'static, ReadDirOperationResult>>,
    metadata_fut: Option<BoxFuture<'static, Result<VfsMetadata, VfsError>>>,
}

impl Unpin for WalkDirIterator {}

impl Stream for WalkDirIterator {
    type Item = VfsResult<AsyncVfsPath>;

    fn poll_next(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        let this = self.get_mut();
        // Check if we have a previously stored result from last call
        // that we could not utilize due to pending path.metadata() call
        let result = if this.prev_result.is_none() {
            loop {
                match this.inner.poll_next_unpin(cx) {
                    Poll::Pending => return Poll::Pending,
                    Poll::Ready(Some(path)) => break Ok(path),
                    Poll::Ready(None) => {
                        let directory = if this.todo.is_empty() {
                            return Poll::Ready(None);
                        } else {
                            this.todo[this.todo.len() - 1].clone()
                        };
                        let mut read_dir_fut = if this.read_dir_fut.is_some() {
                            this.read_dir_fut.take().unwrap()
                        } else {
                            Box::pin(async move { directory.read_dir().await })
                        };
                        match read_dir_fut.poll_unpin(cx) {
                            Poll::Pending => {
                                this.read_dir_fut = Some(read_dir_fut);
                                return Poll::Pending;
                            }
                            Poll::Ready(Err(err)) => {
                                let _ = this.todo.pop();
                                break Err(err);
                            }
                            Poll::Ready(Ok(iterator)) => {
                                let _ = this.todo.pop();
                                this.inner = iterator;
                            }
                        }
                    }
                }
            }
        } else {
            Ok(this.prev_result.take().unwrap())
        };
        if let Ok(path) = &result {
            let mut metadata_fut = if this.metadata_fut.is_some() {
                this.metadata_fut.take().unwrap()
            } else {
                let path_clone = path.clone();
                Box::pin(async move { path_clone.metadata().await })
            };
            match metadata_fut.poll_unpin(cx) {
                Poll::Pending => {
                    this.prev_result = Some(path.clone());
                    this.metadata_fut = Some(metadata_fut);
                    return Poll::Pending;
                }
                Poll::Ready(Ok(meta)) => {
                    if meta.file_type == VfsFileType::Directory {
                        this.todo.push(path.clone());
                    }
                }
                Poll::Ready(Err(err)) => return Poll::Ready(Some(Err(err))),
            }
        }
        Poll::Ready(Some(result))
    }
}

#[derive(Debug)]
pub enum CopyError {
    ReadError(VfsError),
    WriteError(VfsError),
}

const COPY_BUF_SIZE: usize = 8 * 1024;

pub async fn simple_async_copy<R, W>(reader: &mut R, writer: &mut W) -> Result<u64, CopyError>
where
    R: AsyncSeekAndRead + Unpin + ?Sized,
    W: AsyncSeekAndWrite + Unpin + ?Sized,
{
    let mut buf = [0; COPY_BUF_SIZE];
    let mut total_bytes_copied = 0;
    loop {
        let bytes_read = match reader.read(&mut buf).await {
            Ok(0) => return Ok(total_bytes_copied),
            Ok(n) => n,
            Err(e) => return Err(CopyError::ReadError(e)),
        };

        writer
            .write_all(&buf[..bytes_read])
            .await
            .map_err(CopyError::WriteError)?;
        total_bytes_copied += bytes_read as u64;
    }
}
