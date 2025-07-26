//! Thread-safe mount table implementation for AWKernel
//!
//! This module provides the fundamental building blocks for mount table management
//! with proper synchronization for concurrent access.

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::sync::Arc;
use awkernel_sync::rwlock::RwLock;
use super::block_device::BlockDevice;
use super::mount_types::{
    MountFlags, MountOptions, MountInfo, MountError, path_utils, generate_mount_id
};

/// Represents a single mount point in the system
#[derive(Clone)]
pub struct MountPoint {
    /// The path where the filesystem is mounted
    pub path: String,
    /// The source device or filesystem identifier
    pub source: String,
    /// The filesystem type (e.g., "ext4", "memfs")
    pub fs_type: String,
    /// Mount flags
    pub flags: MountFlags,
    /// Unique mount ID
    pub mount_id: usize,
    /// Optional block device for filesystems that need one
    pub block_device: Option<Arc<dyn BlockDevice>>,
    /// Filesystem-specific options
    pub fs_options: alloc::collections::BTreeMap<String, String>,
}


impl MountPoint {
    /// Create a new mount point
    pub fn new(
        path: String, 
        source: String, 
        fs_type: String, 
        options: MountOptions,
        block_device: Option<Arc<dyn BlockDevice>>,
    ) -> Self {
        let mount_id = generate_mount_id();
        Self {
            path,
            source,
            fs_type,
            flags: options.flags,
            mount_id,
            block_device,
            fs_options: options.fs_options,
        }
    }

    /// Convert to MountInfo
    pub fn to_mount_info(&self) -> MountInfo {
        MountInfo {
            path: self.path.clone(),
            source: self.source.clone(),
            fs_type: self.fs_type.clone(),
            flags: self.flags,
            mount_id: self.mount_id,
            fs_options: self.fs_options.clone(),
        }
    }
}

/// Thread-safe mount table structure
pub struct MountTable {
    /// List of all mount points, protected by RwLock
    mounts: RwLock<Vec<MountPoint>>,
}

impl Default for MountTable {
    fn default() -> Self {
        Self::new()
    }
}

impl MountTable {
    /// Create a new empty mount table
    pub const fn new() -> Self {
        Self {
            mounts: RwLock::new(Vec::new()),
        }
    }


    /// Find the best matching mount for a path
    fn find_best_mount(&self, path: &str) -> Option<MountPoint> {
        let normalized = path_utils::normalize_path(path);
        let mounts = self.mounts.read();
        
        // Find all mounts that are parent paths
        let mut candidates: Vec<_> = mounts
            .iter()
            .filter(|m| path_utils::is_subpath(&m.path, &normalized) || m.path == normalized)
            .collect();
        
        // Sort by path length (longest first) to find the most specific mount
        candidates.sort_by(|a, b| b.path.len().cmp(&a.path.len()));
        
        candidates.first().map(|m| (*m).clone())
    }
}

impl MountTable {
    /// Mount a filesystem at the specified path
    pub fn mount(
        &self,
        path: &str,
        source: &str,
        fs_type: &str,
        options: MountOptions,
    ) -> Result<usize, MountError> {
        let normalized_path = path_utils::normalize_path(path);
        
        // Validate path
        if normalized_path.is_empty() {
            return Err(MountError::InvalidPath("Empty path".into()));
        }
        
        let mut mounts = self.mounts.write();
        
        // Check for duplicate mount paths
        if mounts.iter().any(|m| m.path == normalized_path) {
            return Err(MountError::AlreadyMounted(normalized_path));
        }
        
        // Create new mount point
        let mount = MountPoint::new(
            normalized_path,
            source.to_string(),
            fs_type.to_string(),
            options,
            None,
        );
        
        let mount_id = mount.mount_id;
        mounts.push(mount);
        
        Ok(mount_id)
    }

    /// Unmount a filesystem
    pub fn unmount(&self, path: &str) -> Result<(), MountError> {
        let normalized_path = path_utils::normalize_path(path);
        let mut mounts = self.mounts.write();
        
        // Find the mount index
        let mount_idx = mounts
            .iter()
            .position(|m| m.path == normalized_path)
            .ok_or_else(|| MountError::NotMounted(normalized_path.clone()))?;
        
        mounts.remove(mount_idx);
        
        Ok(())
    }

    /// Get mount information for a path
    pub fn get_mount_info(&self, path: &str) -> Result<MountInfo, MountError> {
        self.find_best_mount(path)
            .map(|m| m.to_mount_info())
            .ok_or_else(|| MountError::NotMounted(path.to_string()))
    }

    /// List all mounted filesystems
    pub fn list_mounts(&self) -> Vec<MountInfo> {
        self.mounts.read()
            .iter()
            .map(|m| m.to_mount_info())
            .collect()
    }

    /// Check if a path is a mount point
    pub fn is_mount_point(&self, path: &str) -> bool {
        let normalized = path_utils::normalize_path(path);
        self.mounts.read()
            .iter()
            .any(|m| m.path == normalized)
    }
}

impl MountTable {
    /// Resolve a path to its block device and relative path
    pub fn resolve_path(&self, path: &str) -> Result<(Arc<dyn BlockDevice>, String, MountInfo), MountError> {
        let normalized_path = path_utils::normalize_path(path);
        
        let mount = self.find_best_mount(&normalized_path)
            .ok_or_else(|| MountError::NotMounted(path.to_string()))?;
        
        let device = mount.block_device.clone()
            .ok_or_else(|| MountError::FilesystemError("No block device".into()))?;
        
        let relative_path = path_utils::relative_path(&mount.path, &normalized_path)
            .unwrap_or_default();
        
        Ok((device, relative_path, mount.to_mount_info()))
    }
}

// Global mount table instance with proper synchronization
use awkernel_sync::mutex::{Mutex, MCSNode};
static MOUNT_TABLE: Mutex<Option<Arc<MountTable>>> = Mutex::new(None);

/// Get or initialize the global mount table
pub fn get_mount_table() -> Arc<MountTable> {
    let mut node = MCSNode::new();
    let mut guard = MOUNT_TABLE.lock(&mut node);
    
    if guard.is_none() {
        *guard = Some(Arc::new(MountTable::new()));
    }
    
    guard.clone().unwrap()
}

/// Initialize the global mount table (for compatibility)
pub fn init_mount_table() -> Arc<MountTable> {
    get_mount_table()
}

/// Mount a filesystem using the global mount table
pub fn mount(
    path: &str,
    source: &str,
    fs_type: &str,
    options: MountOptions,
) -> Result<usize, MountError> {
    get_mount_table().mount(path, source, fs_type, options)
}

/// Unmount a filesystem using the global mount table
pub fn unmount(path: &str) -> Result<(), MountError> {
    get_mount_table().unmount(path)
}

/// Get mount information for a path
pub fn get_mount_info(path: &str) -> Result<MountInfo, MountError> {
    get_mount_table().get_mount_info(path)
}


/// Resolve a path to its mount point and relative path
pub fn resolve_mount_path(path: &str) -> Result<(MountInfo, String), MountError> {
    let table = get_mount_table();
    let normalized_path = path_utils::normalize_path(path);
    
    let mount = table.find_best_mount(&normalized_path)
        .ok_or_else(|| MountError::NotMounted(path.to_string()))?;
    
    let relative_path = path_utils::relative_path(&mount.path, &normalized_path)
        .unwrap_or_default();
    
    Ok((mount.to_mount_info(), relative_path))
}

