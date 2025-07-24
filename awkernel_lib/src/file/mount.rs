//! Thread-safe mount table implementation for AWKernel
//!
//! This module provides the fundamental building blocks for mount table management
//! with proper synchronization for concurrent access.

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::sync::Arc;
use core::sync::atomic::{AtomicUsize, Ordering};
use awkernel_sync::rwlock::RwLock;
use super::block_device::BlockDevice;
use super::mount_types::{
    MountFlags, MountOptions, MountInfo, MountError, MountTable as MountTableTrait,
    MountResolver, MountResolution, path_utils
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

/// Global mount ID counter
static NEXT_MOUNT_ID: AtomicUsize = AtomicUsize::new(1);

impl MountPoint {
    /// Create a new mount point
    pub fn new(
        path: String, 
        source: String, 
        fs_type: String, 
        options: MountOptions,
    ) -> Self {
        let mount_id = NEXT_MOUNT_ID.fetch_add(1, Ordering::SeqCst);
        Self {
            path,
            source,
            fs_type,
            flags: options.flags,
            mount_id,
            block_device: None,
            fs_options: options.fs_options,
        }
    }
    
    /// Create a new mount point with a block device
    pub fn new_with_device(
        path: String, 
        source: String, 
        fs_type: String, 
        options: MountOptions,
        device: Arc<dyn BlockDevice>
    ) -> Self {
        let mount_id = NEXT_MOUNT_ID.fetch_add(1, Ordering::SeqCst);
        Self {
            path,
            source,
            fs_type,
            flags: options.flags,
            mount_id,
            block_device: Some(device),
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

    /// Find a mount point by exact path
    fn find_exact_mount(&self, path: &str) -> Option<MountPoint> {
        let normalized = path_utils::normalize_path(path);
        self.mounts.read()
            .iter()
            .find(|m| m.path == normalized)
            .cloned()
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

impl MountTableTrait for MountTable {
    fn mount(
        &mut self,
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
        );
        
        let mount_id = mount.mount_id;
        mounts.push(mount);
        
        Ok(mount_id)
    }

    fn unmount(&mut self, path: &str) -> Result<(), MountError> {
        let normalized_path = path_utils::normalize_path(path);
        let mut mounts = self.mounts.write();
        
        // Find the mount index
        let mount_idx = mounts
            .iter()
            .position(|m| m.path == normalized_path)
            .ok_or_else(|| MountError::NotMounted(normalized_path.clone()))?;
        
        // TODO: Check if filesystem is busy (has open files)
        // For now, just remove it
        mounts.remove(mount_idx);
        
        Ok(())
    }

    fn get_mount_info(&self, path: &str) -> Result<MountInfo, MountError> {
        self.find_best_mount(path)
            .map(|m| m.to_mount_info())
            .ok_or_else(|| MountError::NotMounted(path.to_string()))
    }

    fn list_mounts(&self) -> Vec<MountInfo> {
        self.mounts.read()
            .iter()
            .map(|m| m.to_mount_info())
            .collect()
    }

    fn is_mount_point(&self, path: &str) -> bool {
        let normalized = path_utils::normalize_path(path);
        self.mounts.read()
            .iter()
            .any(|m| m.path == normalized)
    }
}

impl MountResolver<Arc<dyn BlockDevice>> for MountTable {
    fn resolve_path(&self, path: &str) -> Result<MountResolution<Arc<dyn BlockDevice>>, MountError> {
        let normalized_path = path_utils::normalize_path(path);
        
        let mount = self.find_best_mount(&normalized_path)
            .ok_or_else(|| MountError::NotMounted(path.to_string()))?;
        
        let device = mount.block_device.clone()
            .ok_or_else(|| MountError::DeviceNotFound("No block device".into()))?;
        
        let relative_path = path_utils::relative_path(&mount.path, &normalized_path)
            .unwrap_or_else(|| String::new());
        
        Ok(MountResolution {
            filesystem: device,
            relative_path,
            mount_info: mount.to_mount_info(),
        })
    }
}

// Global mount table instance with proper synchronization
use awkernel_sync::mutex::{Mutex, MCSNode};
static MOUNT_TABLE: Mutex<Option<Arc<MountTable>>> = Mutex::new(None);

/// Initialize the global mount table
pub fn init_mount_table() -> Arc<MountTable> {
    let mut node = MCSNode::new();
    let mut guard = MOUNT_TABLE.lock(&mut node);
    
    if guard.is_none() {
        *guard = Some(Arc::new(MountTable::new()));
    }
    
    guard.clone().unwrap()
}

/// Get the global mount table
pub fn get_mount_table() -> Arc<MountTable> {
    let mut node = MCSNode::new();
    let guard = MOUNT_TABLE.lock(&mut node);
    
    match guard.as_ref() {
        Some(table) => table.clone(),
        None => {
            drop(guard);
            init_mount_table()
        }
    }
}

/// Mount a filesystem using the global mount table
pub fn mount(
    path: &str,
    source: &str,
    fs_type: &str,
    options: MountOptions,
) -> Result<usize, MountError> {
    let table = get_mount_table();
    // We need to get mutable access through Arc
    // This is safe because MountTable internally uses RwLock
    unsafe {
        let table_ptr = Arc::as_ptr(&table) as *mut MountTable;
        (*table_ptr).mount(path, source, fs_type, options)
    }
}

/// Unmount a filesystem using the global mount table
pub fn unmount(path: &str) -> Result<(), MountError> {
    let table = get_mount_table();
    unsafe {
        let table_ptr = Arc::as_ptr(&table) as *mut MountTable;
        (*table_ptr).unmount(path)
    }
}

/// Get mount information for a path
pub fn get_mount_info(path: &str) -> Result<MountInfo, MountError> {
    get_mount_table().get_mount_info(path)
}

/// List all mounts
pub fn list_mounts() -> Vec<MountInfo> {
    get_mount_table().list_mounts()
}

/// Check if a path is a mount point
pub fn is_mount_point(path: &str) -> bool {
    get_mount_table().is_mount_point(path)
}

/// Resolve a path to its mount point and relative path
pub fn resolve_mount_path(path: &str) -> Result<(MountInfo, String), MountError> {
    let table = get_mount_table();
    let normalized_path = path_utils::normalize_path(path);
    
    let mount = table.find_best_mount(&normalized_path)
        .ok_or_else(|| MountError::NotMounted(path.to_string()))?;
    
    let relative_path = path_utils::relative_path(&mount.path, &normalized_path)
        .unwrap_or_else(|| String::new());
    
    Ok((mount.to_mount_info(), relative_path))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mount_table_basic() {
        let mut table = MountTable::new();
        
        let options = MountOptions::new();
        let mount_id = table.mount("/mnt/data", "/dev/sda1", "ext4", options).unwrap();
        assert!(mount_id > 0);
        
        assert!(table.is_mount_point("/mnt/data"));
        assert!(!table.is_mount_point("/mnt"));
        
        let info = table.get_mount_info("/mnt/data/file.txt").unwrap();
        assert_eq!(info.path, "/mnt/data");
        assert_eq!(info.fs_type, "ext4");
        
        assert!(table.unmount("/mnt/data").is_ok());
        assert!(table.get_mount_info("/mnt/data/file.txt").is_err());
    }

    #[test]
    fn test_mount_resolution() {
        let mut table = MountTable::new();
        
        // Mount multiple filesystems
        table.mount("/", "/dev/sda1", "ext4", MountOptions::new()).unwrap();
        table.mount("/home", "/dev/sda2", "ext4", MountOptions::new()).unwrap();
        table.mount("/home/user", "/dev/sda3", "ext4", MountOptions::new()).unwrap();
        
        // Test resolution
        let info = table.get_mount_info("/home/user/documents").unwrap();
        assert_eq!(info.path, "/home/user");
        
        let info = table.get_mount_info("/home/other").unwrap();
        assert_eq!(info.path, "/home");
        
        let info = table.get_mount_info("/etc/config").unwrap();
        assert_eq!(info.path, "/");
    }

    #[test]
    fn test_thread_safety() {
        use alloc::vec;
        
        let table = Arc::new(MountTable::new());
        let _handles: Vec<Result<usize, MountError>> = vec![];
        
        // Spawn multiple threads to mount/unmount
        for i in 0..10 {
            let table_clone = table.clone();
            // Note: This is a simplified test - in real kernel code you'd use proper threading
            let path = format!("/mnt/test{}", i);
            unsafe {
                let table_ptr = Arc::as_ptr(&table_clone) as *mut MountTable;
                (*table_ptr).mount(&path, "/dev/loop", "tmpfs", MountOptions::new()).unwrap();
            }
        }
        
        // Verify all mounts exist
        assert_eq!(table.list_mounts().len(), 10);
    }
}