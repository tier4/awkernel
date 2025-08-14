//! Common mount table types and traits shared between sync and async implementations

use alloc::string::String;
use alloc::vec::Vec;
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

/// Filesystem-specific options
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FsOption {
    /// Format the filesystem before mounting (FatFS)
    Format,
    /// Set cluster size for FatFS (in bytes)
    ClusterSize(u32),
    /// Set volume label
    VolumeLabel(String),
    // Future options can be added here:
    // BlockSize(u32),  // for ext4
    // JournalMode(JournalMode), // for ext4
}

/// Collection of filesystem-specific options
#[derive(Debug, Clone, Default)]
pub struct FsOptions {
    options: Vec<FsOption>,
}

impl FsOptions {
    /// Create empty options
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Add an option (builder pattern)
    pub fn with_option(mut self, option: FsOption) -> Self {
        self.options.push(option);
        self
    }
    
    /// Check if a specific option exists
    pub fn contains(&self, option: &FsOption) -> bool {
        self.options.contains(option)
    }
    
    /// Check if format option is set
    pub fn has_format(&self) -> bool {
        self.options.iter().any(|o| matches!(o, FsOption::Format))
    }
    
    /// Get cluster size if specified
    pub fn get_cluster_size(&self) -> Option<u32> {
        self.options.iter().find_map(|o| match o {
            FsOption::ClusterSize(size) => Some(*size),
            _ => None,
        })
    }
    
    /// Get volume label if specified
    pub fn get_volume_label(&self) -> Option<&str> {
        self.options.iter().find_map(|o| match o {
            FsOption::VolumeLabel(label) => Some(label.as_str()),
            _ => None,
        })
    }
}

/// Mount options including flags and filesystem-specific options
#[derive(Debug, Clone, Default)]
pub struct MountOptions {
    /// Standard mount flags
    pub flags: MountFlags,
    /// Filesystem-specific options
    pub fs_options: FsOptions,
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
            fs_options: FsOptions::new(),
        }
    }
    
    /// Builder method to set the format option
    pub fn with_format(mut self) -> Self {
        self.fs_options = self.fs_options.add(FsOption::Format);
        self
    }
    
    /// Builder method to set cluster size
    pub fn with_cluster_size(mut self, size: u32) -> Self {
        self.fs_options = self.fs_options.add(FsOption::ClusterSize(size));
        self
    }
    
    /// Builder method to set volume label
    pub fn with_volume_label(mut self, label: impl Into<String>) -> Self {
        self.fs_options = self.fs_options.add(FsOption::VolumeLabel(label.into()));
        self
    }
    
    /// Builder method to add any filesystem option
    pub fn with_fs_option(mut self, option: FsOption) -> Self {
        self.fs_options = self.fs_options.add(option);
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
    pub fs_options: FsOptions,
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



