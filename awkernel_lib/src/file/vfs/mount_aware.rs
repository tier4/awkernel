//! Mount-aware path handling for the VFS layer
//!
//! This module provides path utilities that are aware of mount points

use alloc::{format, string::{String, ToString}, vec::Vec};
use crate::file::mount::resolve_mount_path;
use crate::file::mount_types::MountInfo;
use core::fmt;

/// A path that is aware of mount points and can resolve its location
/// within the mount hierarchy
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MountAwarePath {
    /// The normalized absolute path
    path: String,
}

impl MountAwarePath {
    /// Create a new mount-aware path
    pub fn new(path: impl AsRef<str>) -> Self {
        let normalized = Self::normalize_path(path.as_ref());
        Self {
            path: normalized,
        }
    }
    
    /// Get the string representation of the path
    pub fn as_str(&self) -> &str {
        &self.path
    }
    
    /// Resolve the mount point and relative path for this path
    pub fn resolve_mount(&self) -> Option<(MountInfo, String)> {
        resolve_mount_path(&self.path).ok()
    }
    
    /// Check if this path crosses a mount boundary when compared to another path
    pub fn crosses_mount_boundary(&self, other: &MountAwarePath) -> bool {
        let self_mount = self.resolve_mount();
        let other_mount = other.resolve_mount();
        
        match (self_mount, other_mount) {
            (Some((m1, _)), Some((m2, _))) => m1.mount_id != m2.mount_id,
            _ => false,
        }
    }
    
    /// Get the filesystem type for this path
    pub fn filesystem_type(&self) -> Option<String> {
        self.resolve_mount().map(|(mount, _)| mount.fs_type.clone())
    }
    
    /// Check if this path is on a read-only mount
    pub fn is_read_only(&self) -> bool {
        self.resolve_mount()
            .map(|(mount, _)| mount.flags.readonly)
            .unwrap_or(false)
    }
    
    /// Join a path segment to this path
    pub fn join(&self, path: impl AsRef<str>) -> Self {
        let joined = if self.path == "/" {
            format!("/{}", path.as_ref().trim_start_matches('/'))
        } else {
            format!("{}/{}", self.path, path.as_ref().trim_start_matches('/'))
        };
        Self::new(&joined)
    }
    
    /// Get the parent path
    pub fn parent(&self) -> Option<Self> {
        if self.path == "/" {
            return None;
        }
        
        let last_slash = self.path.rfind('/')?;
        if last_slash == 0 {
            Some(Self::new("/"))
        } else {
            Some(Self::new(&self.path[..last_slash]))
        }
    }
    
    /// Get the filename portion of the path
    pub fn filename(&self) -> Option<&str> {
        if self.path == "/" {
            return None;
        }
        self.path.rsplit('/').next()
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
                component => components.push(component),
            }
        }
        
        if is_absolute {
            if components.is_empty() {
                "/".to_string()
            } else {
                format!("/{}", components.join("/"))
            }
        } else if components.is_empty() {
            ".".to_string()
        } else {
            components.join("/")
        }
    }
}

impl fmt::Display for MountAwarePath {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.path)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_path_normalization() {
        assert_eq!(MountAwarePath::normalize_path("/"), "/");
        assert_eq!(MountAwarePath::normalize_path("/foo/bar"), "/foo/bar");
        assert_eq!(MountAwarePath::normalize_path("/foo/../bar"), "/bar");
        assert_eq!(MountAwarePath::normalize_path("/foo/./bar"), "/foo/bar");
        assert_eq!(MountAwarePath::normalize_path("/foo/bar/.."), "/foo");
        assert_eq!(MountAwarePath::normalize_path("/../foo"), "/foo");
        assert_eq!(MountAwarePath::normalize_path("foo/bar"), "foo/bar");
        assert_eq!(MountAwarePath::normalize_path("foo/../bar"), "bar");
    }
}