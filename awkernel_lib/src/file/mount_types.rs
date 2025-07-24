//! Common mount table types and traits shared between sync and async implementations

use alloc::string::String;
use alloc::vec::Vec;
use alloc::collections::BTreeMap;
use core::fmt;

/// Mount flags that control filesystem behavior
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct MountFlags {
    /// Mount filesystem as read-only
    pub readonly: bool,
    /// Disallow execution of binaries
    pub noexec: bool,
    /// Ignore setuid/setgid bits
    pub nosuid: bool,
    /// Disallow access to device special files
    pub nodev: bool,
}

impl MountFlags {
    /// Create default mount flags (all false)
    pub const fn new() -> Self {
        Self {
            readonly: false,
            noexec: false,
            nosuid: false,
            nodev: false,
        }
    }

    /// Create read-only mount flags
    pub const fn readonly() -> Self {
        Self {
            readonly: true,
            noexec: false,
            nosuid: false,
            nodev: false,
        }
    }
}

/// Mount options including flags and filesystem-specific options
#[derive(Debug, Clone, Default)]
pub struct MountOptions {
    /// Standard mount flags
    pub flags: MountFlags,
    /// Filesystem-specific options (e.g., "uid=1000", "umask=0022")
    pub fs_options: BTreeMap<String, String>,
}

impl MountOptions {
    /// Create new mount options with default flags
    pub fn new() -> Self {
        Self::default()
    }

    /// Create mount options with specific flags
    pub fn with_flags(flags: MountFlags) -> Self {
        Self {
            flags,
            fs_options: BTreeMap::new(),
        }
    }

    /// Add a filesystem-specific option
    pub fn add_option(&mut self, key: impl Into<String>, value: impl Into<String>) {
        self.fs_options.insert(key.into(), value.into());
    }
}

/// Information about a mounted filesystem
#[derive(Debug, Clone)]
pub struct MountInfo {
    /// Mount point path
    pub path: String,
    /// Source device or path
    pub source: String,
    /// Filesystem type (e.g., "fatfs", "ext4")
    pub fs_type: String,
    /// Mount flags
    pub flags: MountFlags,
    /// Unique mount identifier
    pub mount_id: usize,
    /// Filesystem-specific options
    pub fs_options: BTreeMap<String, String>,
}

/// Result of path resolution against mount table
#[derive(Debug)]
pub struct MountResolution<T> {
    /// The filesystem instance
    pub filesystem: T,
    /// Path relative to the mount point
    pub relative_path: String,
    /// Mount information
    pub mount_info: MountInfo,
}

/// Errors that can occur during mount operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MountError {
    /// Mount point already in use
    AlreadyMounted(String),
    /// Mount point not found
    NotMounted(String),
    /// Invalid mount path
    InvalidPath(String),
    /// Filesystem type not supported
    UnsupportedFilesystem(String),
    /// Device not found or inaccessible
    DeviceNotFound(String),
    /// Filesystem is busy (has open files)
    Busy(String),
    /// Permission denied
    PermissionDenied,
    /// Generic I/O error
    IoError(String),
    /// Mount table not initialized
    NotInitialized,
}

impl fmt::Display for MountError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlreadyMounted(path) => write!(f, "Path already mounted: {}", path),
            Self::NotMounted(path) => write!(f, "Path not mounted: {}", path),
            Self::InvalidPath(path) => write!(f, "Invalid mount path: {}", path),
            Self::UnsupportedFilesystem(fs) => write!(f, "Unsupported filesystem: {}", fs),
            Self::DeviceNotFound(dev) => write!(f, "Device not found: {}", dev),
            Self::Busy(path) => write!(f, "Mount point busy: {}", path),
            Self::PermissionDenied => write!(f, "Permission denied"),
            Self::IoError(msg) => write!(f, "I/O error: {}", msg),
            Self::NotInitialized => write!(f, "Mount table not initialized"),
        }
    }
}

/// Trait for mount table operations
pub trait MountTable {
    /// Mount a filesystem at the specified path
    fn mount(
        &mut self,
        path: &str,
        source: &str,
        fs_type: &str,
        options: MountOptions,
    ) -> Result<usize, MountError>;

    /// Unmount a filesystem
    fn unmount(&mut self, path: &str) -> Result<(), MountError>;

    /// Get mount information for a path
    fn get_mount_info(&self, path: &str) -> Result<MountInfo, MountError>;

    /// List all mounted filesystems
    fn list_mounts(&self) -> Vec<MountInfo>;

    /// Check if a path is a mount point
    fn is_mount_point(&self, path: &str) -> bool;
}

/// Trait for resolving paths to filesystems
pub trait MountResolver<T> {
    /// Resolve a path to its filesystem and relative path
    fn resolve_path(&self, path: &str) -> Result<MountResolution<T>, MountError>;
}

/// Helper functions for path operations
pub mod path_utils {
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;
    use alloc::format;

    /// Normalize a path by resolving . and .. components
    pub fn normalize_path(path: &str) -> String {
        let mut components = Vec::new();
        
        for component in path.split('/').filter(|s| !s.is_empty()) {
            match component {
                "." => {} // Skip current directory
                ".." => { components.pop(); } // Go up one level
                _ => components.push(component),
            }
        }
        
        if components.is_empty() {
            "/".to_string()
        } else {
            format!("/{}", components.join("/"))
        }
    }

    /// Check if a path is a subpath of another
    pub fn is_subpath(parent: &str, child: &str) -> bool {
        let parent = normalize_path(parent);
        let child = normalize_path(child);
        
        // Special case: root is parent of everything except itself
        if parent == "/" {
            return true; // Everything is a subpath of root
        }
        
        child.starts_with(&parent) && 
        (child.len() == parent.len() || child.chars().nth(parent.len()) == Some('/'))
    }

    /// Get the relative path from parent to child
    pub fn relative_path(parent: &str, child: &str) -> Option<String> {
        let parent = normalize_path(parent);
        let child = normalize_path(child);
        
        if !is_subpath(&parent, &child) {
            return None;
        }
        
        if parent == "/" {
            Some(child[1..].to_string())
        } else if child.len() > parent.len() + 1 {
            Some(child[parent.len() + 1..].to_string())
        } else {
            Some(String::new())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::path_utils::*;
    use alloc::string::ToString;

    #[test]
    fn test_normalize_path() {
        assert_eq!(normalize_path("/"), "/");
        assert_eq!(normalize_path("/foo/bar"), "/foo/bar");
        assert_eq!(normalize_path("/foo/../bar"), "/bar");
        assert_eq!(normalize_path("/foo/./bar"), "/foo/bar");
        assert_eq!(normalize_path("/foo/bar/.."), "/foo");
        assert_eq!(normalize_path("/../.."), "/");
    }

    #[test]
    fn test_is_subpath() {
        assert!(is_subpath("/", "/foo"));
        assert!(is_subpath("/foo", "/foo/bar"));
        assert!(!is_subpath("/foo", "/foobar"));
        assert!(!is_subpath("/foo/bar", "/foo"));
        assert!(is_subpath("/foo", "/foo"));
    }

    #[test]
    fn test_relative_path() {
        assert_eq!(relative_path("/", "/foo"), Some("foo".to_string()));
        assert_eq!(relative_path("/foo", "/foo/bar"), Some("bar".to_string()));
        assert_eq!(relative_path("/foo", "/foo"), Some("".to_string()));
        assert_eq!(relative_path("/foo", "/bar"), None);
    }
}