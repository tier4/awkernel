//! High-level mount management API
//!
//! This module provides a high-level API for managing filesystem mounts,
//! including filesystem factories and mount options.

use alloc::boxed::Box;
use alloc::collections::BTreeMap;
use alloc::string::{String, ToString};
use alloc::sync::Arc;
use alloc::vec::Vec;
use core::fmt::Debug;

use super::block_device::BlockDevice;
use super::mount::{MountFlags, MountPoint, init_mount_table, with_mount_table_mut};

/// Mount options that can be passed to mount operations
#[derive(Debug, Clone)]
pub struct MountOptions {
    /// Basic mount flags
    pub flags: MountFlags,
    /// Filesystem-specific options
    pub fs_options: BTreeMap<String, String>,
}

impl Default for MountOptions {
    fn default() -> Self {
        Self {
            flags: MountFlags::default(),
            fs_options: BTreeMap::new(),
        }
    }
}

impl MountOptions {
    /// Create new mount options with default flags
    pub fn new() -> Self {
        Self::default()
    }
    
    /// Set read-only flag
    pub fn read_only(mut self, value: bool) -> Self {
        self.flags.readonly = value;
        self
    }
    
    /// Set noexec flag
    pub fn no_exec(mut self, value: bool) -> Self {
        self.flags.noexec = value;
        self
    }
    
    /// Add a filesystem-specific option
    pub fn with_option(mut self, key: impl Into<String>, value: impl Into<String>) -> Self {
        self.fs_options.insert(key.into(), value.into());
        self
    }
}

/// Error type for mount operations
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
    /// No mount table initialized
    NoMountTable,
}

/// Result type for mount operations
pub type MountResult<T> = Result<T, MountError>;

/// Trait for filesystem factories
pub trait FileSystemFactory: Send + Sync {
    /// Create a new filesystem instance
    fn create(
        &self,
        device: Option<Arc<dyn BlockDevice>>,
        options: &MountOptions,
    ) -> MountResult<()>;
    
    /// Get the filesystem type name
    fn fs_type(&self) -> &str;
}

/// FAT filesystem factory
pub struct FatFsFactory;

impl FileSystemFactory for FatFsFactory {
    fn create(
        &self,
        device: Option<Arc<dyn BlockDevice>>,
        _options: &MountOptions,
    ) -> MountResult<()> {
        // For now, we support two cases:
        // 1. No device provided - use the global memory FAT filesystem
        // 2. Device provided - would need to be a concrete type to use with create_fatfs_from_block_device
        
        if device.is_some() {
            // In a real implementation, we would need to handle different concrete device types
            // For now, we don't support mounting with external devices through this factory
            return Err(MountError::FilesystemError(
                "Mounting FAT with external devices not yet implemented through factory".into()
            ));
        }
        
        // Use the global memory FAT filesystem
        // This is initialized separately through init_memory_fatfs()
        Ok(())
    }
    
    fn fs_type(&self) -> &str {
        "fatfs"
    }
}

/// Global registry of filesystem factories
static mut FS_FACTORIES: Option<BTreeMap<String, Box<dyn FileSystemFactory>>> = None;
static FS_FACTORIES_INIT: core::sync::atomic::AtomicBool = 
    core::sync::atomic::AtomicBool::new(false);

/// Initialize the filesystem factory registry
fn init_fs_factories() {
    use core::sync::atomic::Ordering;
    
    if !FS_FACTORIES_INIT.swap(true, Ordering::SeqCst) {
        unsafe {
            FS_FACTORIES = Some(BTreeMap::new());
        }
    }
}

/// Register a filesystem factory
pub fn register_filesystem(factory: Box<dyn FileSystemFactory>) -> MountResult<()> {
    init_fs_factories();
    
    unsafe {
        if let Some(factories) = &mut FS_FACTORIES {
            let fs_type = factory.fs_type().to_string();
            factories.insert(fs_type, factory);
            Ok(())
        } else {
            Err(MountError::NoMountTable)
        }
    }
}

/// Mount manager providing high-level mount operations
pub struct MountManager;

impl MountManager {
    /// Initialize the mount system
    pub fn init() {
        init_mount_table();
        init_fs_factories();
        
        // Register default filesystems
        let _ = register_filesystem(Box::new(FatFsFactory));
    }
    
    /// Mount a filesystem
    pub fn mount(
        path: impl Into<String>,
        source: impl Into<String>,
        fs_type: impl Into<String>,
        device: Option<Arc<dyn BlockDevice>>,
        options: MountOptions,
    ) -> MountResult<()> {
        let path = path.into();
        let source = source.into();
        let fs_type = fs_type.into();
        
        // Validate path
        if !path.starts_with('/') {
            return Err(MountError::InvalidPath(path));
        }
        
        // Check if filesystem type is registered
        let factory = unsafe {
            FS_FACTORIES.as_ref()
                .and_then(|f| f.get(&fs_type))
                .ok_or_else(|| MountError::UnknownFilesystem(fs_type.clone()))?
        };
        
        // Create the filesystem
        factory.create(device.clone(), &options)?;
        
        // Create mount point
        let mount_point = if let Some(device) = device {
            MountPoint::new_with_device(path.clone(), source, fs_type, options.flags, device)
        } else {
            MountPoint::new(path.clone(), source, fs_type, options.flags)
        };
        
        // Add to mount table
        with_mount_table_mut(|table| {
            table.mount(mount_point)
                .map_err(|_| MountError::AlreadyMounted(path.clone()))
        })
        .ok_or(MountError::NoMountTable)?
    }
    
    /// Unmount a filesystem
    pub fn unmount(path: impl AsRef<str>) -> MountResult<()> {
        let path = path.as_ref();
        
        with_mount_table_mut(|table| {
            table.unmount(path)
                .map_err(|_| MountError::NotMounted(path.to_string()))
        })
        .ok_or(MountError::NoMountTable)?
    }
    
    /// List all mount points
    pub fn list_mounts() -> Vec<MountInfo> {
        with_mount_table_mut(|table| {
            table.get_all_mounts()
                .iter()
                .map(|m| MountInfo {
                    path: m.path.clone(),
                    source: m.source.clone(),
                    fs_type: m.fs_type.clone(),
                    flags: m.flags,
                    has_device: m.block_device.is_some(),
                })
                .collect()
        })
        .unwrap_or_default()
    }
    
    /// Get mount information for a path
    pub fn get_mount_info(path: impl AsRef<str>) -> Option<MountInfo> {
        let path = path.as_ref();
        
        with_mount_table_mut(|table| {
            table.find_mount(path).map(|m| MountInfo {
                path: m.path.clone(),
                source: m.source.clone(),
                fs_type: m.fs_type.clone(),
                flags: m.flags,
                has_device: m.block_device.is_some(),
            })
        })
        .flatten()
    }
}

/// Mount information
#[derive(Debug, Clone)]
pub struct MountInfo {
    /// Mount path
    pub path: String,
    /// Source device or identifier
    pub source: String,
    /// Filesystem type
    pub fs_type: String,
    /// Mount flags
    pub flags: MountFlags,
    /// Whether a block device is attached
    pub has_device: bool,
}

/// Convenience function to mount root filesystem
pub fn mount_root() -> MountResult<()> {
    MountManager::mount(
        "/",
        "rootfs",
        "fatfs",
        None,
        MountOptions::new(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_mount_options() {
        let opts = MountOptions::new()
            .read_only(true)
            .no_exec(true)
            .with_option("noatime", "true");
        
        assert!(opts.flags.readonly);
        assert!(opts.flags.noexec);
        assert_eq!(opts.fs_options.get("noatime"), Some(&"true".to_string()));
    }
}