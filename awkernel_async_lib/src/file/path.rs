//! Virtual filesystem path (async version)
//!
//! The virtual file system abstraction generalizes over file systems and allow using
//! different VirtualFileSystem implementations (i.e. an in memory implementation for unit tests)
use super::filesystem::AsyncFileSystem;
use awkernel_lib::{
    file::{
        error::IoError,
        fatfs::{fs::LossyOemCpConverter, time::NullTimeProvider},
        memfs::{InMemoryDisk, InMemoryDiskError},
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
use core::fmt::Debug;
use core::{
    pin::Pin,
    task::{Context, Poll},
};
use futures::{future::BoxFuture, stream::BoxStream, FutureExt, Stream, StreamExt};

use embedded_io_async::{Read, Seek, SeekFrom, Write};

// AsyncVfs は、ラップする AsyncFileSystem の具体的な型についてジェネリックになります。
struct AsyncVfs<FS: AsyncFileSystem> {
    fs: Box<FS>, // Box<dyn AsyncFileSystem> ではなく Box<FS>
}

/// A virtual filesystem path, identifying a single file or directory in this virtual filesystem
#[derive(Clone)]
// AsyncVfsPath も AsyncFileSystem の具体的な型についてジェネリックになります。
pub struct AsyncVfsPath<FS: AsyncFileSystem> {
    path: Arc<str>,
    fs: Arc<AsyncVfs<FS>>,
}

// PathLike トレイトの実装で、Error 型を FS::Error に変更
impl<FS: AsyncFileSystem> PathLike for AsyncVfsPath<FS> {
    type Error = FS::Error;
    fn get_path(&self) -> String {
        self.path.to_string()
    }
}

// PartialEq と Eq の実装もジェネリックパラメータ FS に対応
impl<FS: AsyncFileSystem> PartialEq for AsyncVfsPath<FS> {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path && Arc::ptr_eq(&self.fs, &other.fs)
    }
}

impl<FS: AsyncFileSystem> Eq for AsyncVfsPath<FS> {}

// new_in_memory_fatfs は AsyncFatFs の具体的な型に依存するため、
// FS の型が InMemoryDiskError を Error に持つ AsyncFatFs であることを前提とします。
// AsyncFatFs が実際にどのように定義されているか不明なため、これは仮定です。
// 通常は、`AsyncVfsPath<impl AsyncFileSystem<Error = InMemoryDiskError>>` のようには書けないため、
// 具体的な AsyncFatFs の型をここで使うことになります。
// 例: `AsyncVfsPath<crate::file::fatfs::InMemoryFatFs>` のように。
// ここでは一般的なジェネリックな `FS` を使うパターンを維持します。
impl
    AsyncVfsPath<
        crate::file::fatfs::AsyncFatFs<InMemoryDisk, NullTimeProvider, LossyOemCpConverter>,
    >
{
    // Assuming AsyncFatFs is the concrete type
    pub fn new_in_memory_fatfs() -> Self {
        let fs = crate::file::fatfs::AsyncFatFs::new_in_memory();
        // new 関数が FS を直接受け取るように変更されたため、それに合わせる
        AsyncVfsPath::new(fs)
    }
}

// AsyncVfsPath のメソッド実装ブロックも FS: AsyncFileSystem に基づく
impl<FS> AsyncVfsPath<FS>
where
    FS: AsyncFileSystem + 'static, // FS 自体も Send + Sync + 'static の要件を持つはず
    FS::Error: Clone + Send + Sync + Debug + 'static, // エラー型にも必要なトレイト境界を追加
{
    /// Creates a root path for the given filesystem
    // new 関数が T: AsyncFileSystem ではなく、直接 FS を受け取るように変更
    pub fn new(filesystem: FS) -> Self {
        AsyncVfsPath {
            path: "".into(),
            fs: Arc::new(AsyncVfs {
                fs: Box::new(filesystem),
            }),
        }
    }

    /// Returns the string representation of this path
    pub fn as_str(&self) -> &str {
        &self.path
    }

    /// Appends a path segment to this path, returning the result
    pub fn join(&self, path: impl AsRef<str>) -> VfsResult<Self, FS::Error> {
        // E を FS::Error に変更
        let new_path = self.join_internal(&self.path, path.as_ref())?;
        Ok(Self {
            path: Arc::from(new_path),
            fs: self.fs.clone(),
        })
    }

    /// Returns the root path of this filesystem
    pub fn root(&self) -> Self {
        AsyncVfsPath {
            path: "".into(),
            fs: self.fs.clone(),
        }
    }

    /// Returns true if this is the root path
    pub fn is_root(&self) -> bool {
        self.path.is_empty()
    }

    /// Creates the directory at this path
    pub async fn create_dir(&self) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        self.get_parent("create directory").await?;
        self.fs.fs.create_dir(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not create directory".to_string())
        })
    }

    /// Creates the directory at this path, also creating parent directories as necessary
    pub async fn create_dir_all(&self) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
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
    ) -> VfsResult<Pin<Box<dyn Stream<Item = Self> + Send + Unpin + 'static>>, FS::Error> {
        // E を FS::Error に変更
        let parent = self.path.clone();
        let fs = self.fs.clone();
        let stream = self
            .fs
            .fs
            .read_dir(&self.path)
            .await
            .map_err(|err| {
                err.with_path(&*self.path)
                    .with_context(|| "Could not read directory".to_string())
            })?
            .map(move |path_str| Self {
                path: format!("{parent}/{path_str}").into(),
                fs: fs.clone(),
            });
        Ok(Box::pin(stream))
    }

    /// Creates a file at this path for writing, overwriting any existing file
    // 戻り値の型を FS::WriteFile に変更
    pub async fn create_file(&self) -> VfsResult<FS::WriteFile, FS::Error> {
        self.get_parent("create file").await?;
        self.fs.fs.create_file(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not create file".to_string())
        })
    }

    /// Opens the file at this path for reading
    // 戻り値の型を FS::ReadFile に変更
    pub async fn open_file(&self) -> VfsResult<FS::ReadFile, FS::Error> {
        self.fs.fs.open_file(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not open file".to_string())
        })
    }

    /// Checks whether parent is a directory
    async fn get_parent(&self, action: &str) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        let parent = self.parent();
        if !parent.exists().await? {
            return Err(VfsError::from(VfsErrorKind::Other(format!(
                "Could not {action}, parent directory does not exist"
            )))
            .with_path(&*self.path));
        }
        let metadata = parent.metadata().await?;
        if metadata.file_type != VfsFileType::Directory {
            return Err(VfsError::from(VfsErrorKind::Other(format!(
                "Could not {action}, parent path is not a directory"
            )))
            .with_path(&*self.path));
        }
        Ok(())
    }

    /// Opens the file at this path for appending
    // 戻り値の型を FS::AppendFile に変更
    pub async fn append_file(&self) -> VfsResult<FS::WriteFile, FS::Error> {
        self.fs.fs.append_file(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not open file for appending".to_string())
        })
    }

    /// Removes the file at this path
    pub async fn remove_file(&self) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        self.fs.fs.remove_file(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not remove file".to_string())
        })
    }

    /// Removes the directory at this path
    pub async fn remove_dir(&self) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        self.fs.fs.remove_dir(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not remove directory".to_string())
        })
    }

    /// Ensures that the directory at this path is removed, recursively deleting all contents if necessary
    pub async fn remove_dir_all(&self) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
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
    pub async fn metadata(&self) -> VfsResult<VfsMetadata, FS::Error> {
        // E を FS::Error に変更
        self.fs.fs.metadata(&self.path).await.map_err(|err| {
            err.with_path(&*self.path)
                .with_context(|| "Could not get metadata".to_string())
        })
    }

    /// Sets the files creation timestamp at this path
    pub async fn set_creation_time(&self, time: Time) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        self.fs
            .fs
            .set_creation_time(&self.path, time)
            .await
            .map_err(|err| {
                err.with_path(&*self.path)
                    .with_context(|| "Could not set creation timestamp.".to_string())
            })
    }

    /// Sets the files modification timestamp at this path
    pub async fn set_modification_time(&self, time: Time) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        self.fs
            .fs
            .set_modification_time(&self.path, time)
            .await
            .map_err(|err| {
                err.with_path(&*self.path)
                    .with_context(|| "Could not set modification timestamp.".to_string())
            })
    }

    /// Sets the files access timestamp at this path
    pub async fn set_access_time(&self, time: Time) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        self.fs
            .fs
            .set_access_time(&self.path, time)
            .await
            .map_err(|err| {
                err.with_path(&*self.path)
                    .with_context(|| "Could not set access timestamp.".to_string())
            })
    }

    /// Returns `true` if the path exists and is pointing at a regular file, otherwise returns `false`.
    pub async fn is_file(&self) -> VfsResult<bool, FS::Error> {
        // E を FS::Error に変更
        if !self.exists().await? {
            return Ok(false);
        }
        let metadata = self.metadata().await?;
        Ok(metadata.file_type == VfsFileType::File)
    }

    /// Returns `true` if the path exists and is pointing at a directory, otherwise returns `false`.
    pub async fn is_dir(&self) -> VfsResult<bool, FS::Error> {
        // E を FS::Error に変更
        if !self.exists().await? {
            return Ok(false);
        }
        let metadata = self.metadata().await?;
        Ok(metadata.file_type == VfsFileType::Directory)
    }

    /// Returns true if a file or directory exists at this path, false otherwise
    pub async fn exists(&self) -> VfsResult<bool, FS::Error> {
        // E を FS::Error に変更
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
            path: parent_path.into(),
            fs: self.fs.clone(),
        }
    }

    /// Recursively iterates over all the directories and files at this path
    pub async fn walk_dir(&self) -> VfsResult<WalkDirIterator<FS>, FS::Error> {
        // E を FS::Error に変更
        Ok(WalkDirIterator {
            inner: self.read_dir().await?,
            todo: vec![],
            //_pending_meta: None,
            //pending_read: None,
            prev_result: None,
            metadata_fut: None,
            read_dir_fut: None,
        })
    }

    /// Reads a complete file to a string
    pub async fn read_to_string(&self) -> VfsResult<String, FS::Error> {
        // E を FS::Error に変更
        let metadata = self.metadata().await?;
        if metadata.file_type != VfsFileType::File {
            return Err(
                VfsError::from(VfsErrorKind::Other("Path is a directory".into()))
                    .with_path(&*self.path)
                    .with_context(|| "Could not read path"),
            );
        }
        let mut buffer = vec![0; metadata.len as usize];
        self.open_file()
            .await?
            .read_exact(&mut buffer)
            .await
            .map_err(|_| VfsError::from(VfsErrorKind::Other("ReadExactError".into())))?; // TODO: ReadExactError mapping

        String::from_utf8(buffer).map_err(|_| {
            VfsError::from(VfsErrorKind::Other("Invalid UTF-8 sequence".into()))
                .with_path(&*self.path)
                .with_context(|| "Could not read path as string")
        })
    }

    /// Copies a file to a new destination
    pub async fn copy_file(&self, destination: &AsyncVfsPath<FS>) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        async {
            if destination.exists().await? {
                return Err(
                    VfsError::from(VfsErrorKind::FileExists).with_path(&*destination.path).with_context(|| {
                        "Destination exists already".to_string()
                    }),
                );
            }
            if Arc::ptr_eq(&self.fs, &destination.fs) {
                let result = self.fs.fs.copy_file(&self.path, &destination.path).await;
                if !matches!(result, Err(ref err) if matches!(err.kind(), VfsErrorKind::NotSupported))
                {
                    return result;
                }
            }
            let mut src = self.open_file().await?; // FS::ReadFile 型
            let mut dest = destination.create_file().await?; // FS::WriteFile 型
            simple_async_copy(&mut src, &mut dest).await.map_err(|err| match err {
                CopyError::ReadError(e) => e,
                CopyError::WriteError(e) => e,
            })?;
            Ok(())
        }
        .await
        .map_err(|err| {
            err.with_path(&*self.path).with_context(|| {
                format!("Could not copy '{}' to '{}'", self.as_str(), destination.as_str())
            })
        })
    }

    /// Moves or renames a file to a new destination
    pub async fn move_file(&self, destination: &AsyncVfsPath<FS>) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        async {
            if destination.exists().await? {
                return Err(VfsError::from(VfsErrorKind::FileExists).with_path(&*destination.path).with_context(|| {
                    "Destination exists already".to_string()
                }));
            }
            if Arc::ptr_eq(&self.fs, &destination.fs) {
                let result = self.fs.fs.move_file(&self.path, &destination.path).await;
                if !matches!(result, Err(ref err) if matches!(err.kind(), VfsErrorKind::NotSupported))
                {
                    return result;
                }
            }
            let mut src = self.open_file().await?; // FS::ReadFile 型
            let mut dest = destination.create_file().await?; // FS::WriteFile 型
            simple_async_copy(&mut src, &mut dest).await.map_err(|err| match err {
                CopyError::ReadError(e) => e,
                CopyError::WriteError(e) => e,
            })?;
            self.remove_file().await?;
            Ok(())
        }
        .await
        .map_err(|err| {
            err.with_path(&*self.path).with_context(|| {
                format!("Could not move '{}' to '{}'", self.as_str(), destination.as_str())
            })
        })
    }

    /// Copies a directory to a new destination, recursively
    pub async fn copy_dir(&self, destination: &AsyncVfsPath<FS>) -> VfsResult<u64, FS::Error> {
        // E を FS::Error に変更
        let files_copied = async {
            let mut files_copied = 0u64;
            if destination.exists().await? {
                return Err(VfsError::from(VfsErrorKind::FileExists)
                    .with_path(&*destination.path)
                    .with_context(|| "Destination exists already".to_string()));
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
        .map_err(|err: VfsError<FS::Error>| {
            // ここも FS::Error に変更
            err.with_path(&*self.path).with_context(|| {
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
    pub async fn move_dir(&self, destination: &AsyncVfsPath<FS>) -> VfsResult<(), FS::Error> {
        // E を FS::Error に変更
        async {
            if destination.exists().await? {
                return Err(
                    VfsError::from(VfsErrorKind::FileExists).with_path(&*destination.path).with_context(|| {
                        "Destination exists already".to_string()
                    }),
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
        .map_err(|err: VfsError<FS::Error>| { // ここも FS::Error に変更
            err.with_path(&*self.path).with_context(|| {
                format!(
                    "Could not move directory '{}' to '{}'",
                    self.as_str(),
                    destination.as_str()
                )
            })
        })
    }
}

/// An iterator for recursively walking a file hierarchy
// WalkDirIterator もジェネリックパラメータを FS に変更
pub struct WalkDirIterator<FS: AsyncFileSystem> {
    inner: BoxStream<'static, AsyncVfsPath<FS>>, // AsyncVfsPath<E> から AsyncVfsPath<FS> へ
    todo: Vec<AsyncVfsPath<FS>>,                 // AsyncVfsPath<E> から AsyncVfsPath<FS> へ
    prev_result: Option<AsyncVfsPath<FS>>,
    // Used to store futures when poll_next returns pending
    // this ensures a new future is not spawned on each poll.
    //read_dir_fut: Option<
    //BoxFuture<
    //'static,
    //Result<Box<(dyn Stream<Item = AsyncVfsPath<FS>> + Send + Unpin)>, VfsError<FS::Error>>,
    //>,
    //>,
    read_dir_fut: Option<
        BoxFuture<
            'static,
            // Result の中身を Pin<Box<dyn Stream<Item = AsyncVfsPath<FS>> + Send + Unpin>> に変更
            Result<
                Pin<Box<dyn Stream<Item = AsyncVfsPath<FS>> + Send + Unpin + 'static>>,
                VfsError<FS::Error>,
            >,
        >,
    >,
    metadata_fut: Option<BoxFuture<'static, Result<VfsMetadata, VfsError<FS::Error>>>>,
}

// Unpin 実装もジェネリックパラメータ FS に対応
impl<FS: AsyncFileSystem + 'static> Unpin for WalkDirIterator<FS> where
    FS::Error: Clone + Send + Sync + 'static
{
}

// Stream 実装もジェネリックパラメータ FS に対応
impl<FS: AsyncFileSystem + 'static> Stream for WalkDirIterator<FS>
where
    FS::Error: Clone + Send + Sync + Debug + 'static,
{
    type Item = VfsResult<AsyncVfsPath<FS>, FS::Error>; // E を FS::Error に変更

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

// CopyError もジェネリックパラメータ FS::Error に対応
#[derive(Debug)]
pub enum CopyError<E: IoError> {
    ReadError(E),
    WriteError(E),
}

const COPY_BUF_SIZE: usize = 8 * 1024;

// simple_async_copy は Read, Write, Seek トレイトを直接使用するように変更
pub async fn simple_async_copy<E, R, W>(reader: &mut R, writer: &mut W) -> Result<u64, CopyError<E>>
where
    E: IoError + Clone + Send + Sync + 'static, // エラー型に必要
    R: Read<Error = E> + Seek<Error = E> + Unpin + ?Sized, // embedded_io_async::Read/Seek を直接指定
    W: Write<Error = E> + Seek<Error = E> + Unpin + ?Sized, // embedded_io_async::Write/Seek を直接指定
{
    let mut buf = [0; COPY_BUF_SIZE];
    let mut total_bytes_copied = 0;
    loop {
        let bytes_read = match reader.read(&mut buf).await {
            Ok(0) => return Ok(total_bytes_copied),
            Ok(n) => n,
            Err(e) => {
                return Err(CopyError::ReadError(e));
            }
        };

        writer
            .write_all(&buf[..bytes_read])
            .await
            .map_err(CopyError::WriteError)?;
        total_bytes_copied += bytes_read as u64;
    }
}
