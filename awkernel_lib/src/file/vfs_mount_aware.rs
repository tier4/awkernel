//! Mount-aware path operations for VFS
//!
//! This module provides path operations that understand mount points
//! and can handle operations across filesystem boundaries.

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use crate::file::mount::{resolve_mount_path, MountPoint};

/// A path that is aware of mount points and filesystem boundaries
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MountAwarePath {
    /// The normalized path
    path: String,
    /// Cached mount point information
    mount_info: Option<(MountPoint, String)>,
}

impl MountAwarePath {
    /// Create a new mount-aware path
    pub fn new(path: impl AsRef<str>) -> Self {
        let normalized = Self::normalize_path(path.as_ref());
        let mount_info = resolve_mount_path(&normalized);
        
        Self {
            path: normalized,
            mount_info,
        }
    }
    
    /// Get the path as a string
    pub fn as_str(&self) -> &str {
        &self.path
    }
    
    /// Normalize a path by resolving . and .. components
    fn normalize_path(path: &str) -> String {
        let mut components = Vec::new();
        let is_absolute = path.starts_with('/');
        
        for component in path.split('/') {
            match component {
                "" | "." => continue,
                ".." => {
                    if !components.is_empty() && components.last() != Some(&"..") {
                        components.pop();
                    } else if !is_absolute {
                        components.push("..");
                    }
                }
                comp => components.push(comp),
            }
        }
        
        if is_absolute {
            let mut result = String::from("/");
            result.push_str(&components.join("/"));
            if result.len() > 1 && result.ends_with('/') {
                result.pop();
            }
            result
        } else {
            components.join("/")
        }
    }
    
    /// Join this path with another path component
    pub fn join(&self, other: impl AsRef<str>) -> Self {
        let other = other.as_ref();
        let new_path = if other.starts_with('/') {
            other.to_string()
        } else {
            format!("{}/{}", self.path, other)
        };
        
        Self::new(new_path)
    }
    
    /// Get the parent directory path
    pub fn parent(&self) -> Option<Self> {
        if self.path == "/" {
            return None;
        }
        
        let pos = self.path.rfind('/')?;
        if pos == 0 {
            Some(Self::new("/"))
        } else {
            Some(Self::new(&self.path[..pos]))
        }
    }
    
    /// Get the filename component
    pub fn filename(&self) -> Option<&str> {
        if self.path == "/" {
            return None;
        }
        
        self.path.rsplit('/').next().filter(|s| !s.is_empty())
    }
    
    /// Resolve this path to mount point and relative path
    pub fn resolve_mount(&self) -> Option<(&MountPoint, &str)> {
        self.mount_info.as_ref().map(|(mount, relative)| {
            (mount, relative.as_str())
        })
    }
    
    /// Get the filesystem type for this path
    pub fn filesystem_type(&self) -> Option<&str> {
        self.mount_info.as_ref().map(|(mount, _)| mount.fs_type.as_str())
    }
    
    /// Check if this path is on a read-only mount
    pub fn is_read_only(&self) -> bool {
        self.mount_info.as_ref()
            .map(|(mount, _)| mount.flags.readonly)
            .unwrap_or(false)
    }
    
    /// Check if this path is on a no-exec mount
    pub fn is_no_exec(&self) -> bool {
        self.mount_info.as_ref()
            .map(|(mount, _)| mount.flags.noexec)
            .unwrap_or(false)
    }
    
    /// Check if two paths cross a mount boundary
    pub fn crosses_mount_boundary(&self, other: &MountAwarePath) -> bool {
        match (&self.mount_info, &other.mount_info) {
            (Some((mount1, _)), Some((mount2, _))) => mount1.path != mount2.path,
            _ => false,
        }
    }
    
    /// Get the mount path for this path
    pub fn mount_path(&self) -> Option<&str> {
        self.mount_info.as_ref().map(|(mount, _)| mount.path.as_str())
    }
    
    /// Get the relative path within the mount
    pub fn relative_path(&self) -> Option<&str> {
        self.mount_info.as_ref().map(|(_, relative)| relative.as_str())
    }
}

impl From<&str> for MountAwarePath {
    fn from(path: &str) -> Self {
        Self::new(path)
    }
}

impl From<String> for MountAwarePath {
    fn from(path: String) -> Self {
        Self::new(path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_normalize_path() {
        assert_eq!(MountAwarePath::normalize_path("/a/b/c"), "/a/b/c");
        assert_eq!(MountAwarePath::normalize_path("/a/./b/c"), "/a/b/c");
        assert_eq!(MountAwarePath::normalize_path("/a/b/../c"), "/a/c");
        assert_eq!(MountAwarePath::normalize_path("/a/b/../../c"), "/c");
        assert_eq!(MountAwarePath::normalize_path("/a/b/../../../c"), "/c");
        assert_eq!(MountAwarePath::normalize_path("/../a"), "/a");
        assert_eq!(MountAwarePath::normalize_path("a/b/c"), "a/b/c");
        assert_eq!(MountAwarePath::normalize_path("a/../b"), "b");
        assert_eq!(MountAwarePath::normalize_path("../a/b"), "../a/b");
    }
    
    #[test]
    fn test_path_operations() {
        let path = MountAwarePath::new("/a/b/c");
        
        assert_eq!(path.join("d").as_str(), "/a/b/c/d");
        assert_eq!(path.join("../d").as_str(), "/a/b/d");
        assert_eq!(path.join("/x/y").as_str(), "/x/y");
        
        assert_eq!(path.parent().map(|p| p.as_str()), Some("/a/b"));
        assert_eq!(path.filename(), Some("c"));
        
        let root = MountAwarePath::new("/");
        assert_eq!(root.parent(), None);
        assert_eq!(root.filename(), None);
    }
}