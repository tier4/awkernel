//! Async virtual filesystem path
//!
//! This module provides AsyncVfsPath that automatically resolves filesystems 
//! from the VFS registry based on mount points.

use super::{
    filesystem::{AsyncFileSystem, AsyncSeekAndRead, AsyncSeekAndWrite},
    mount::resolve_filesystem_for_path,
};
use crate::time::Time;
use alloc::{
    boxed::Box,
    format,
    string::{String, ToString},
    sync::Arc,
    vec,
    vec::Vec,
};
use awkernel_lib::file::{
    path_utils,
    vfs::error::{VfsError, VfsErrorKind, VfsResult},
};
use async_recursion::async_recursion;
use core::{
    pin::Pin,
    task::{Context, Poll},
};
use futures::{Stream, StreamExt};

/// A trait for common path behavior
pub trait PathLike: Clone {
    fn get_path(&self) -> String;
    
    fn filename_internal(&self) -> String {
        path_utils::filename(&self.get_path())
    }

    fn extension_internal(&self) -> Option<String> {
        path_utils::extension(&self.get_path())
    }

    fn parent_internal(&self, path: &str) -> String {
        path_utils::parent_path(path)
    }

    fn join_internal(&self, in_path: &str, path: &str) -> VfsResult<String> {
        path_utils::join_path(in_path, path)
            .map_err(|_msg| VfsError::from(VfsErrorKind::InvalidPath).with_path(path))
    }
}

/// Type of file
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum VfsFileType {
    /// A plain file
    File,
    /// A Directory
    Directory,
}

/// File metadata information
#[derive(Debug)]
pub struct VfsMetadata {
    /// The type of file
    pub file_type: VfsFileType,
    /// Length of the file in bytes, 0 for directories
    pub len: u64,
    /// Creation time of the file, if supported by the vfs implementation
    pub created: Option<Time>,
    /// Modification time of the file, if supported by the vfs implementation
    pub modified: Option<Time>,
    /// Access time of the file, if supported by the vfs implementation
    pub accessed: Option<Time>,
}

/// A virtual filesystem path
#[derive(Clone, Debug)]
pub struct AsyncVfsPath {
    /// The full absolute path
    path: String,
}

impl PathLike for AsyncVfsPath {
    fn get_path(&self) -> String {
        self.path.clone()
    }
}

impl PartialEq for AsyncVfsPath {
    fn eq(&self, other: &Self) -> bool {
        self.path == other.path
    }
}

impl Eq for AsyncVfsPath {}

impl AsyncVfsPath {
    /// Create a new mount-aware path
    pub fn new(path: impl Into<String>) -> Self {
        let mut path = path.into();
        // Ensure path starts with /
        if !path.starts_with('/') && !path.is_empty() {
            path = format!("/{path}");
        }
        Self { path }
    }
    
    /// Resolve the filesystem and relative path for this path
    fn resolve(&self) -> VfsResult<(Arc<dyn AsyncFileSystem>, String)> {
        let (fs, _mount_path, relative_path) = resolve_filesystem_for_path(&self.path)
            .ok_or_else(|| VfsError::from(VfsErrorKind::Other(format!("No filesystem mounted for path: {}", self.path))))?;
        Ok((fs, relative_path))
    }
    
    /// Get the parent path
    pub fn parent(&self) -> Option<Self> {
        let path = self.path.trim_end_matches('/');
        if path.is_empty() || path == "/" {
            return None;
        }
        
        match path.rfind('/') {
            Some(0) => Some(Self::new("/")),
            Some(pos) => Some(Self::new(&path[..pos])),
            None => None,
        }
    }
    
    /// Join a path component
    pub fn join(&self, path: impl AsRef<str>) -> VfsResult<Self> {
        let path = path.as_ref();
        if path.starts_with('/') {
            // Absolute path
            Ok(Self::new(path))
        } else {
            // Relative path
            let mut full_path = self.path.clone();
            if !full_path.ends_with('/') && !full_path.is_empty() {
                full_path.push('/');
            }
            full_path.push_str(path);
            Ok(Self::new(full_path))
        }
    }
    
    /// Get the filename component
    pub fn filename(&self) -> Option<String> {
        let path = self.path.trim_end_matches('/');
        path.rfind('/').map(|pos| path[pos + 1..].to_string())
    }
    
    /// Check if path exists
    pub async fn exists(&self) -> VfsResult<bool> {
        let (fs, rel_path) = self.resolve()?;
        fs.exists(&rel_path).await
    }
    
    /// Get metadata
    pub async fn metadata(&self) -> VfsResult<VfsMetadata> {
        let (fs, rel_path) = self.resolve()?;
        fs.metadata(&rel_path).await
    }
    
    /// Check if this is a directory
    pub async fn is_dir(&self) -> VfsResult<bool> {
        Ok(self.metadata().await?.file_type == VfsFileType::Directory)
    }
    
    /// Check if this is a file
    pub async fn is_file(&self) -> VfsResult<bool> {
        Ok(self.metadata().await?.file_type == VfsFileType::File)
    }
    
    /// Create a directory
    pub async fn create_dir(&self) -> VfsResult<()> {
        let (fs, rel_path) = self.resolve()?;
        fs.create_dir(&rel_path).await
    }
    
    /// Create a directory and all parent directories
    #[async_recursion]
    pub async fn create_dir_all(&self) -> VfsResult<()> {
        if self.exists().await? {
            return if self.is_dir().await? {
                Ok(())
            } else {
                Err(VfsError::from(VfsErrorKind::Other(
                    "Path exists but is not a directory".into(),
                )))
            };
        }
        
        if let Some(parent) = self.parent() {
            parent.create_dir_all().await?;
        }
        
        self.create_dir().await
    }
    
    /// Read directory contents
    pub async fn read_dir(&self) -> VfsResult<Vec<Self>> {
        let (fs, rel_path) = self.resolve()?;
        let stream = fs.read_dir(&rel_path).await?;
        
        let entries: Vec<String> = stream.collect().await;
        let mut paths = Vec::new();
        
        for entry in entries {
            paths.push(self.join(&entry)?);
        }
        
        Ok(paths)
    }
    
    /// Open file for reading
    pub async fn open_file(&self) -> VfsResult<Box<dyn AsyncSeekAndRead + Send + Unpin>> {
        let (fs, rel_path) = self.resolve()?;
        fs.open_file(&rel_path).await
    }
    
    /// Create file for writing
    pub async fn create_file(&self) -> VfsResult<Box<dyn AsyncSeekAndWrite + Send + Unpin>> {
        let (fs, rel_path) = self.resolve()?;
        fs.create_file(&rel_path).await
    }
    
    /// Append to file
    pub async fn append_file(&self) -> VfsResult<Box<dyn AsyncSeekAndWrite + Send + Unpin>> {
        let (fs, rel_path) = self.resolve()?;
        fs.append_file(&rel_path).await
    }
    
    /// Remove file
    pub async fn remove_file(&self) -> VfsResult<()> {
        let (fs, rel_path) = self.resolve()?;
        fs.remove_file(&rel_path).await
    }
    
    /// Remove directory
    pub async fn remove_dir(&self) -> VfsResult<()> {
        let (fs, rel_path) = self.resolve()?;
        fs.remove_dir(&rel_path).await
    }
    
    /// Remove directory and all contents
    #[async_recursion]
    pub async fn remove_dir_all(&self) -> VfsResult<()> {
        if !self.exists().await? {
            return Ok(());
        }
        
        if self.is_dir().await? {
            let entries = self.read_dir().await?;
            for entry in entries {
                if entry.is_dir().await? {
                    entry.remove_dir_all().await?;
                } else {
                    entry.remove_file().await?;
                }
            }
            self.remove_dir().await
        } else {
            self.remove_file().await
        }
    }
    
    /// Copy file
    pub async fn copy_file(&self, dest: &Self) -> VfsResult<()> {
        // Check if both paths are on the same filesystem
        let (src_fs, src_rel) = self.resolve()?;
        let (dest_fs, dest_rel) = dest.resolve()?;
        
        if Arc::ptr_eq(&src_fs, &dest_fs) {
            // Same filesystem, try native copy
            match src_fs.copy_file(&src_rel, &dest_rel).await {
                Ok(()) => return Ok(()),
                Err(e) if matches!(e.kind(), VfsErrorKind::NotSupported) => {
                    // Fall through to manual copy
                }
                Err(e) => return Err(e),
            }
        }
        
        // Manual copy across filesystems or when not supported
        let mut reader = self.open_file().await?;
        let mut writer = dest.create_file().await?;
        
        let mut buffer = vec![0u8; 8192];
        loop {
            let n = reader.read(&mut buffer).await?;
            if n == 0 {
                break;
            }
            writer.write_all(&buffer[..n]).await?;
        }
        writer.flush().await?;
        
        Ok(())
    }
    
    /// Move file
    pub async fn move_file(&self, dest: &Self) -> VfsResult<()> {
        // Check if both paths are on the same filesystem
        let (src_fs, src_rel) = self.resolve()?;
        let (dest_fs, dest_rel) = dest.resolve()?;
        
        if Arc::ptr_eq(&src_fs, &dest_fs) {
            // Same filesystem, try native move
            match src_fs.move_file(&src_rel, &dest_rel).await {
                Ok(()) => return Ok(()),
                Err(e) if matches!(e.kind(), VfsErrorKind::NotSupported) => {
                    // Fall through to copy+delete
                }
                Err(e) => return Err(e),
            }
        }
        
        // Copy then delete
        self.copy_file(dest).await?;
        self.remove_file().await?;
        
        Ok(())
    }
    
    /// Set creation time
    pub async fn set_creation_time(&self, time: Time) -> VfsResult<()> {
        let (fs, rel_path) = self.resolve()?;
        fs.set_creation_time(&rel_path, time).await
    }
    
    /// Set modification time
    pub async fn set_modification_time(&self, time: Time) -> VfsResult<()> {
        let (fs, rel_path) = self.resolve()?;
        fs.set_modification_time(&rel_path, time).await
    }
    
    /// Set access time
    pub async fn set_access_time(&self, time: Time) -> VfsResult<()> {
        let (fs, rel_path) = self.resolve()?;
        fs.set_access_time(&rel_path, time).await
    }
}

/// Stream adapter for reading directory entries
pub struct ReadDirStream {
    path: AsyncVfsPath,
    inner: Pin<Box<dyn Stream<Item = String> + Send>>,
}

impl Stream for ReadDirStream {
    type Item = VfsResult<AsyncVfsPath>;
    
    fn poll_next(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Option<Self::Item>> {
        match self.inner.as_mut().poll_next(cx) {
            Poll::Ready(Some(name)) => {
                let child_path = self.path.join(name);
                Poll::Ready(Some(child_path))
            }
            Poll::Ready(None) => Poll::Ready(None),
            Poll::Pending => Poll::Pending,
        }
    }
}

