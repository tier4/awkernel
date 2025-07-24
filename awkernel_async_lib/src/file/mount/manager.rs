//! High-level mount management API
//!
//! This module provides the main API for mounting and unmounting filesystems.

use super::{
    factory::{get_filesystem_factory, init_default_factories},
    registry::{init_mount_registry, register_mount, unregister_mount},
    types::{MountError, MountInfo, MountOptions, MountResult},
};
use alloc::{
    format,
    string::String,
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::file::block_device::BlockDevice;

/// Mount manager providing high-level mount operations
pub struct MountManager;

impl MountManager {
    /// Initialize the mount system
    pub fn init() -> MountResult<()> {
        init_mount_registry();
        init_default_factories();
        Ok(())
    }
    
    /// Mount a filesystem
    pub async fn mount(
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
        
        // Get the filesystem factory
        let factory = get_filesystem_factory(&fs_type)?;
        
        // Create the filesystem instance
        let filesystem = factory.create(device, &options).await?;
        
        // Register in the mount registry
        register_mount(path, source, fs_type, options.flags, filesystem)?;
        
        Ok(())
    }
    
    /// Unmount a filesystem
    pub fn unmount(path: impl AsRef<str>) -> MountResult<()> {
        unregister_mount(path.as_ref())
    }
    
    /// List all mount points
    pub fn list_mounts() -> Vec<MountInfo> {
        use super::registry::list_mounts as list_mounts_internal;
        list_mounts_internal()
    }
    
    /// Get mount information for a path
    pub fn get_mount_info(path: impl AsRef<str>) -> MountResult<MountInfo> {
        super::registry::get_mount_info(path.as_ref())
    }
}

/// Convenience function to mount a memory-backed FatFs filesystem
pub async fn mount_memory_fatfs(
    path: impl Into<String>,
    size: usize,
) -> MountResult<()> {
    let path = path.into();
    let source = format!("memory:{size}");
    
    use super::types::mount_options_ext;
    let options = mount_options_ext::with_format(
        mount_options_ext::with_size(MountOptions::new(), size),
        true
    );
    
    MountManager::mount(
        path,
        source,
        "fatfs",
        None, // No device = use memory
        options,
    ).await
}

/// Convenience function to mount root filesystem
pub async fn mount_root() -> MountResult<()> {
    // Create a 1MB memory FatFs filesystem for root
    mount_memory_fatfs("/", 1024 * 1024).await
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[tokio::test]
    async fn test_mount_manager_init() {
        assert!(MountManager::init().is_ok());
    }
}