//! Common mount table types and traits shared between sync and async implementations

use alloc::string::{String, ToString};
use alloc::collections::BTreeMap;
use core::fmt;
use core::sync::atomic::{AtomicUsize, Ordering};

/// Global mount ID counter
static NEXT_MOUNT_ID: AtomicUsize = AtomicUsize::new(1);

/// Generate a new unique mount ID
pub fn generate_mount_id() -> usize {
    NEXT_MOUNT_ID.fetch_add(1, Ordering::SeqCst)
}

/// Mount flags that control filesystem behavior
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct MountFlags {
    /// Mount filesystem as read-only
    pub readonly: bool,
    /// Disallow execution of binaries
    pub noexec: bool,
}

impl MountFlags {
    /// Create default mount flags (all false)
    pub const fn new() -> Self {
        Self {
            readonly: false,
            noexec: false,
        }
    }

    /// Create read-only mount flags
    pub const fn readonly() -> Self {
        Self {
            readonly: true,
            noexec: false,
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
    
    /// Builder method to set the format option
    pub fn with_format(mut self) -> Self {
        self.fs_options.insert("format".to_string(), "true".to_string());
        self
    }
    
    /// Builder method to set read-only flag
    pub fn with_readonly(mut self) -> Self {
        self.flags.readonly = true;
        self
    }
    
    /// Builder method to set noexec flag
    pub fn with_noexec(mut self) -> Self {
        self.flags.noexec = true;
        self
    }
    
    /// Builder method to add a custom option
    pub fn with_option(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.fs_options.insert(key.into(), value.into());
        self
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
    /// Filesystem-specific error
    FilesystemError(String),
}

impl fmt::Display for MountError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::AlreadyMounted(path) => write!(f, "Path already mounted: {path}"),
            Self::NotMounted(path) => write!(f, "Path not mounted: {path}"),
            Self::InvalidPath(path) => write!(f, "Invalid mount path: {path}"),
            Self::UnsupportedFilesystem(fs) => write!(f, "Unsupported filesystem: {fs}"),
            Self::FilesystemError(err) => write!(f, "Filesystem error: {err}"),
        }
    }
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

