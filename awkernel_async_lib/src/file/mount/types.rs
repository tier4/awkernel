//! Types for the async mount system
//!
//! This module re-exports common types from the sync mount system and adds
//! async-specific extensions.

use alloc::string::{String, ToString};
use core::fmt;

// Re-export common types from sync lib
pub use awkernel_lib::file::mount_types::{
    MountFlags, MountOptions, MountInfo,
};

/// Error type for async mount operations
#[derive(Debug, Clone)]
pub enum MountError {
    /// Filesystem type not registered
    UnknownFilesystem(String),
    /// Mount point already exists
    AlreadyMounted(String),
    /// Mount point not found
    NotMounted(String),
    /// Invalid mount point path
    InvalidPath(String),
    /// Filesystem-specific error
    FilesystemError(String),
    /// Mount registry not initialized
    RegistryNotInitialized,
    /// Factory not found
    FactoryNotFound(String),
}

impl fmt::Display for MountError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            MountError::UnknownFilesystem(fs) => write!(f, "Unknown filesystem type: {fs}"),
            MountError::AlreadyMounted(path) => write!(f, "Path already mounted: {path}"),
            MountError::NotMounted(path) => write!(f, "Path not mounted: {path}"),
            MountError::InvalidPath(path) => write!(f, "Invalid mount path: {path}"),
            MountError::FilesystemError(err) => write!(f, "Filesystem error: {err}"),
            MountError::RegistryNotInitialized => write!(f, "Mount registry not initialized"),
            MountError::FactoryNotFound(fs) => write!(f, "No factory registered for filesystem: {fs}"),
        }
    }
}

/// Result type for mount operations
pub type MountResult<T> = Result<T, MountError>;

/// Helper functions for working with MountOptions
pub mod mount_options_ext {
    use super::*;
    
    /// Set read-only flag
    pub fn read_only(mut options: MountOptions, value: bool) -> MountOptions {
        options.flags.readonly = value;
        options
    }
    
    /// Set noexec flag
    pub fn no_exec(mut options: MountOptions, value: bool) -> MountOptions {
        options.flags.noexec = value;
        options
    }
    
    /// Set size for memory filesystems
    pub fn with_size(mut options: MountOptions, size: usize) -> MountOptions {
        options.add_option("size", size.to_string());
        options
    }
    
    /// Get size option
    pub fn get_size(options: &MountOptions) -> Option<usize> {
        options.fs_options.get("size")
            .and_then(|s| s.parse().ok())
    }
    
    /// Set format option
    pub fn with_format(mut options: MountOptions, format: bool) -> MountOptions {
        options.add_option("format", format.to_string());
        options
    }
    
    /// Get format option
    pub fn get_format(options: &MountOptions) -> Option<bool> {
        options.fs_options.get("format")
            .map(|s| s == "true")
    }
}