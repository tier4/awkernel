//! Unified mount registry that tracks both mount points and filesystem instances
//!
//! This provides an optimized mount registry with trie-based path lookup and
//! better data structures for performance.

use super::{MountError, MountResult, MountOptions};
use crate::file::{
    filesystem::AsyncFileSystem,
    fatfs::AsyncFatFs,
};
use alloc::{
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{
    storage::StorageDevice,
    file::{
        fatfs::create_fatfs_from_block_device,
        memfs::MemoryBlockDevice,
        mount_types::{
            MountInfo, path_utils, generate_mount_id,
        },
    },
    sync::rwlock::RwLock,
};

/// Filesystem type for FAT filesystem
pub const FS_TYPE_FATFS: &str = "fatfs";


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
use awkernel_lib::sync::mutex::{Mutex, MCSNode};
static REGISTRY: Mutex<Option<Arc<MountRegistry>>> = Mutex::new(None);

/// Get the global mount registry, initializing if needed
pub(super) fn get_registry() -> Arc<MountRegistry> {
    let mut node = MCSNode::new();
    let mut guard = REGISTRY.lock(&mut node);
    
    if guard.is_none() {
        *guard = Some(Arc::new(MountRegistry::new()));
    }
    
    guard.clone().expect("Registry was just initialized")
}


/// Type alias for the resolve result
type ResolveResult = Result<(Arc<dyn AsyncFileSystem>, String, String), MountError>;

/// Resolve a filesystem for a given path by finding the longest matching mount point
pub fn resolve_filesystem_for_path(path: &str) -> ResolveResult {
    let registry = get_registry();
    
    let (mount_path, entry) = registry.find_best_mount(path)
        .ok_or_else(|| MountError::NotMounted(path.to_string()))?;
    
    let relative_path = path_utils::relative_path(&mount_path, path)
        .unwrap_or_default();
    
    Ok((
        entry.filesystem.clone(),
        mount_path,
        relative_path,
    ))
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

/// Mount a filesystem
pub async fn mount(
    path: impl Into<String>,
    source: impl Into<String>,
    fs_type: impl Into<String>,
    device: Arc<dyn StorageDevice>,
    options: MountOptions,
) -> MountResult<()> {
    let path = path.into();
    let source = source.into();
    let fs_type = fs_type.into();
    
    // Create the filesystem instance
    let filesystem = create_filesystem(&fs_type, device, &options).await?;
    
    // Get the registry and register the mount
    let registry = get_registry();
    registry.register_mount(path, source, fs_type, options, Arc::from(filesystem))?;
    
    Ok(())
}

/// Unmount a filesystem
pub fn unmount(path: impl AsRef<str>) -> MountResult<()> {
    let registry = get_registry();
    registry.unregister_mount(path.as_ref())
}

/// Create a filesystem based on type
async fn create_filesystem(
    fs_type: &str,
    device: Arc<dyn StorageDevice>,
    options: &MountOptions,
) -> MountResult<Box<dyn AsyncFileSystem>> {
    match fs_type {
        FS_TYPE_FATFS => {
            // Try to downcast to concrete types that FatFS supports
            if let Some(memory_device) = device.as_any().downcast_ref::<MemoryBlockDevice>() {
                // Memory block device - use direct approach
                let device_arc = Arc::new(memory_device.clone());
                let format = options.fs_options.get("format")
                    .map(|v| v == "true")
                    .unwrap_or(false);
                
                let fs = create_fatfs_from_block_device(device_arc, format)
                    .map_err(MountError::FilesystemError)?;
                
                Ok(Box::new(AsyncFatFs { fs: Arc::new(fs) }))
            } else {
                // For other devices, we would need a concrete type wrapper
                // Currently only MemoryBlockDevice is supported directly
                Err(MountError::FilesystemError(
                    "FatFS currently only supports MemoryBlockDevice directly. Other devices need concrete type wrappers.".to_string()
                ))
            }
        }
        
        // Future filesystems can be added here
        // "ext4" => create_ext4_filesystem(device, options),
        // "btrfs" => create_btrfs_filesystem(device, options),
        
        _ => Err(MountError::UnsupportedFilesystem(fs_type.to_string()))
    }
}

/// Check if a filesystem type is supported
pub fn is_filesystem_supported(fs_type: &str) -> bool {
    matches!(fs_type, FS_TYPE_FATFS)
}