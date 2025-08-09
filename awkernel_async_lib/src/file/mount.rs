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
        fatfs::create_fatfs_from_block_device,
        memfs::MemoryBlockDevice,
        mount_types::{
            MountInfo, MountOptions, MountError, path_utils, generate_mount_id,
        },
    },
    sync::{
        rwlock::RwLock,
        mutex::{Mutex, MCSNode},
    },
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
    mounts: RwLock<BTreeMap<String, MountEntry>>,
}

impl Default for MountRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl MountRegistry {
    /// Create a new mount registry
    pub fn new() -> Self {
        Self {
            mounts: RwLock::new(BTreeMap::new()),
        }
    }

    /// Find the best matching mount for a path
    fn find_best_mount(&self, path: &str) -> Option<(String, MountEntry)> {
        let normalized = path_utils::normalize_path(path);
        let mounts = self.mounts.read();
        
        // Find longest matching prefix
        mounts
            .range(..=normalized.clone())
            .rev()
            .find(|(mount_path, _)| {
                path_utils::is_subpath(mount_path, &normalized)
            })
            .map(|(k, v)| (k.clone(), v.clone()))
    }

    /// Register a new mount
    pub fn register_mount(
        &self,
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
        let mut mounts = self.mounts.write();
        
        // Check if already mounted
        if mounts.contains_key(&normalized_path) {
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
        mounts.insert(normalized_path, entry);
        Ok(())
    }

    /// Unregister a mount
    pub fn unregister_mount(&self, path: &str) -> Result<(), MountError> {
        let normalized_path = path_utils::normalize_path(path);
        
        let mut mounts = self.mounts.write();
        
        // Remove mount if it exists
        mounts.remove(&normalized_path)
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
        self.mounts.read()
            .values()
            .map(|entry| entry.info.clone())
            .collect()
    }
    
    /// Check if a path is exactly a mount point
    pub fn is_mount_point(&self, path: &str) -> bool {
        let normalized = path_utils::normalize_path(path);
        self.mounts.read().contains_key(&normalized)
    }
}

// Global mount registry instance
static REGISTRY: Mutex<Option<Arc<MountRegistry>>> = Mutex::new(None);

/// Get the global mount registry, initializing if needed
fn get_registry() -> Arc<MountRegistry> {
    let mut node = MCSNode::new();
    let mut guard = REGISTRY.lock(&mut node);
    
    if guard.is_none() {
        *guard = Some(Arc::new(MountRegistry::new()));
    }
    
    guard.clone().expect("Registry was just initialized")
}

/// Type alias for the resolve result
type ResolveResult = (Arc<dyn AsyncFileSystem>, String, String);

/// Resolve a filesystem for a given path by finding the longest matching mount point
/// Returns (filesystem, mount_path, relative_path)
pub fn resolve_filesystem_for_path(path: &str) -> Option<ResolveResult> {
    let registry = get_registry();
    
    registry.find_best_mount(path).map(|(mount_path, entry)| {
        let relative_path = path_utils::relative_path(&mount_path, path)
            .unwrap_or_default();
        
        (entry.filesystem.clone(), mount_path, relative_path)
    })
}

/// Get mount information for a specific path  
pub fn get_mount_info(path: &str) -> Result<MountInfo, MountError> {
    let registry = get_registry();
    registry.get_mount_info_for_path(path)
        .ok_or_else(|| MountError::NotMounted(path.to_string()))
}

/// List all mounted filesystems
pub fn list_mounts() -> Vec<MountInfo> {
    get_registry().list_all_mounts()
}

/// Mount a filesystem on a storage device
/// The device is managed as dyn StorageDevice, but downcasted when needed (e.g., for FatFS)
pub async fn mount(
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
            // FatFS requires concrete types
            // For now, we can only support MemoryBlockDevice since we can't import NvmeNamespace here
            // The proper solution would be to have a trait-based approach or move mount to a higher-level crate
            
            // Try MemoryBlockDevice
            if let Some(mem_dev) = storage::downcast_storage_device::<MemoryBlockDevice>(device_id) {
                let format = options.fs_options.contains_key("format");
                let fs = create_fatfs_from_block_device(mem_dev, format)
                    .map_err(|e| MountError::FilesystemError(alloc::format!("FatFS creation failed: {}", e)))?;
                Arc::new(AsyncFatFs { fs: Arc::new(fs) })
            }
            // For other device types, we need a different approach
            else {
                // Check device type for better error message
                if let Ok(device_info) = storage::get_storage_device(device_id) {
                    match device_info.device_type {
                        storage::StorageDeviceType::NVMe => {
                            return Err(MountError::FilesystemError(
                                "NVMe devices are not yet supported in async mount. The mount system can only downcast to types available in awkernel_async_lib. Consider implementing a kernel-level mount service.".to_string()
                            ));
                        }
                        _ => {
                            return Err(MountError::FilesystemError(
                                alloc::format!("Device type {:?} not supported for FatFS mounting", device_info.device_type)
                            ));
                        }
                    }
                }
                return Err(MountError::FilesystemError(
                    "Cannot downcast device to a supported type for FatFS".to_string()
                ));
            }
        }
        // Future filesystems that can work with dyn StorageDevice
        // "ext4" => {
        //     // If ext4 can work with dyn StorageDevice, no downcasting needed
        //     let device = storage::get_storage_device_arc(device_id)?;
        //     create_ext4_filesystem(device, options)?
        // }
        _ => return Err(MountError::UnsupportedFilesystem(fs_type))
    };
    
    // Get device info using the standard dyn StorageDevice interface
    let device_info = storage::get_storage_device(device_id)
        .map_err(|_| MountError::FilesystemError(alloc::format!("Device ID {} not found", device_id)))?;
    
    // Register the mount
    let registry = get_registry();
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
    let registry = get_registry();
    registry.unregister_mount(path.as_ref())
}

/// Check if a filesystem type is supported
pub fn is_filesystem_supported(fs_type: &str) -> bool {
    matches!(fs_type, FS_TYPE_FATFS)
}