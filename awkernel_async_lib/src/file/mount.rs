//! Unified async mount system for AWKernel
//!
//! This module provides all mount-related functionality including:
//! - Mount registry that tracks both mount points and filesystem instances
//! - High-level mount management API with downcasting support
//! - Mount-aware path resolution

use crate::file::{
    filesystem::AsyncFileSystem,
    fatfs::AsyncFatFs,
};
use alloc::{
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{
    storage::{self},
    file::{
        block_device_adapter::BlockDeviceAdapter,
        fatfs::create_fatfs_from_adapter,
        mount_types::{
            MountInfo, MountOptions, MountError, generate_mount_id,
        },
        path_utils,
    },
    sync::rwlock::RwLock,
};

/// Result type for mount operations
pub type MountResult<T> = Result<T, MountError>;

/// Filesystem type for FAT filesystem
pub const FS_TYPE_FATFS: &str = "fatfs";

// Re-export commonly used types
pub use awkernel_lib::file::mount_types::{MountFlags as MountFlagsExport, MountOptions as MountOptionsExport, MountInfo as MountInfoExport, MountError as MountErrorExport};
pub use awkernel_lib::file::memfs::{create_memory_block_device, DEFAULT_BLOCK_SIZE};

/// A mount entry containing both metadata and filesystem instance
#[derive(Clone)]
struct MountEntry {
    /// Mount information
    info: MountInfo,
    /// The actual filesystem instance
    filesystem: Arc<dyn AsyncFileSystem>,
}

impl MountEntry {
    fn new(info: MountInfo, filesystem: Arc<dyn AsyncFileSystem>) -> Self {
        Self {
            info,
            filesystem,
        }
    }
}

/// Mount registry with path lookup
pub struct MountRegistry {
    /// Mount entries indexed by normalized path
    mounts: BTreeMap<String, MountEntry>,
}

impl Default for MountRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl MountRegistry {
    /// Create a new mount registry
    pub const fn new() -> Self {
        Self {
            mounts: BTreeMap::new(),
        }
    }

    /// Find the best matching mount for a path
    fn find_best_mount(&self, path: &str) -> Option<(String, MountEntry)> {
        let normalized = path_utils::normalize_path(path);
        
        // Find longest matching prefix
        self.mounts
            .range(..=normalized.clone())
            .rev()
            .find(|(mount_path, _)| {
                path_utils::is_subpath(mount_path, &normalized)
            })
            .map(|(k, v)| (k.clone(), v.clone()))
    }

    /// Register a new mount
    pub fn register_mount(
        &mut self,
        path: String,
        source: String,
        fs_type: String,
        options: MountOptions,
        filesystem: Arc<dyn AsyncFileSystem>,
    ) -> Result<(), MountError> {
        // Validate path before normalization
        if !path.starts_with('/') {
            return Err(MountError::InvalidPath(path));
        }
        
        let normalized_path = path_utils::normalize_path(&path);
        
        // Check if already mounted
        if self.mounts.contains_key(&normalized_path) {
            return Err(MountError::AlreadyMounted(normalized_path));
        }
        
        // Create mount info
        let mount_id = generate_mount_id();
        let info = MountInfo {
            path: normalized_path.clone(),
            source,
            fs_type,
            flags: options.flags,
            mount_id,
            fs_options: options.fs_options,
        };
        
        let entry = MountEntry::new(info, filesystem);
        self.mounts.insert(normalized_path, entry);
        Ok(())
    }

    /// Unregister a mount
    pub fn unregister_mount(&mut self, path: &str) -> Result<(), MountError> {
        let normalized_path = path_utils::normalize_path(path);
        
        // Remove mount if it exists
        self.mounts.remove(&normalized_path)
            .ok_or(MountError::NotMounted(normalized_path))?;
        Ok(())
    }

    /// Get filesystem for a path
    pub fn get_filesystem(&self, path: &str) -> Option<Arc<dyn AsyncFileSystem>> {
        self.find_best_mount(path)
            .map(|(_, entry)| entry.filesystem.clone())
    }

    /// Get mount information for a path
    pub fn get_mount_info_for_path(&self, path: &str) -> Option<MountInfo> {
        self.find_best_mount(path)
            .map(|(_, entry)| entry.info.clone())
    }
    
    /// List all mounted filesystems
    pub fn list_all_mounts(&self) -> Vec<MountInfo> {
        self.mounts
            .values()
            .map(|entry| entry.info.clone())
            .collect()
    }
    
    /// Check if a path is exactly a mount point
    pub fn is_mount_point(&self, path: &str) -> bool {
        let normalized = path_utils::normalize_path(path);
        self.mounts.contains_key(&normalized)
    }
}

// Global mount registry instance
static REGISTRY: RwLock<MountRegistry> = RwLock::new(MountRegistry {
    mounts: BTreeMap::new(),
});

/// Type alias for the resolve result
type ResolveResult = (Arc<dyn AsyncFileSystem>, String, String);

/// Resolve a filesystem for a given path by finding the longest matching mount point
/// Returns (filesystem, mount_path, relative_path)
pub fn resolve_filesystem_for_path(path: &str) -> Option<ResolveResult> {
    let registry = REGISTRY.read();
    
    registry.find_best_mount(path).map(|(mount_path, entry)| {
        let relative_path = path_utils::relative_path(&mount_path, path)
            .unwrap_or_default();
        
        (entry.filesystem.clone(), mount_path, relative_path)
    })
}

/// Get mount information for a specific path  
pub fn get_mount_info(path: &str) -> Result<MountInfo, MountError> {
    let registry = REGISTRY.read();
    registry.get_mount_info_for_path(path)
        .ok_or_else(|| MountError::NotMounted(path.to_string()))
}

/// List all mounted filesystems
pub fn list_mounts() -> Vec<MountInfo> {
    REGISTRY.read().list_all_mounts()
}

/// Mount a filesystem on a storage device
/// The device is managed as dyn StorageDevice, but downcasted when needed (e.g., for FatFS)
pub fn mount(
    path: impl Into<String>,
    device_id: u64,
    fs_type: impl Into<String>,
    options: MountOptions,
) -> MountResult<()> {
    let path = path.into();
    let fs_type = fs_type.into();
    
    // Create filesystem based on type
    let filesystem: Arc<dyn AsyncFileSystem> = match fs_type.as_str() {
        FS_TYPE_FATFS => {
            // Use DynBlockDeviceAdapter for all device types
            // This works with any StorageDevice implementation (Memory, NVMe, etc.)
            
            // Get the device as dyn StorageDevice
            let device = storage::get_storage_device(device_id)
                .map_err(|_| MountError::FilesystemError(alloc::format!("Device ID {device_id} not found")))?;
            
            let format = options.fs_options.has_format();
            
            // Create BlockDeviceAdapter that works with any device type
            let adapter = BlockDeviceAdapter::new(device);
            
            // Create FatFS using the adapter
            let fs = create_fatfs_from_adapter(adapter, format)
                .map_err(|e| MountError::FilesystemError(alloc::format!("FatFS creation failed: {e}")))?;
            
            Arc::new(AsyncFatFs { fs: Arc::new(fs) })
        }
        // Future filesystems that can work with dyn StorageDevice
        // "ext4" => {
        //     // If ext4 can work with dyn StorageDevice, no downcasting needed
        //     let device = storage::get_storage_device(device_id)?;
        //     create_ext4_filesystem(device, options)?
        // }
        _ => return Err(MountError::UnsupportedFilesystem(fs_type))
    };
    
    // Get device info using the standard dyn StorageDevice interface
    let device_info = storage::get_storage_status(device_id)
        .map_err(|_| MountError::FilesystemError(alloc::format!("Device ID {device_id} not found")))?;
    
    // Register the mount
    let mut registry = REGISTRY.write();
    registry.register_mount(
        path,
        device_info.device_name.into_owned(),
        fs_type,
        options,
        filesystem
    )?;
    
    Ok(())
}

/// Unmount a filesystem
pub fn unmount(path: impl AsRef<str>) -> MountResult<()> {
    let mut registry = REGISTRY.write();
    registry.unregister_mount(path.as_ref())
}

/// Check if a filesystem type is supported
pub fn is_filesystem_supported(fs_type: &str) -> bool {
    matches!(fs_type, FS_TYPE_FATFS)
}