//! Basic mount table implementation for AWKernel
//!
//! This module provides the fundamental building blocks for mount table management
//! without VFS integration.

use alloc::string::{String, ToString};
use alloc::vec::Vec;
use alloc::sync::Arc;
use alloc::format;
use core::sync::atomic::{AtomicUsize, Ordering};
use super::block_device::BlockDevice;

/// Mount flags that control filesystem behavior
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MountFlags {
    /// Mount read-only
    pub readonly: bool,
    /// Disable execution of binaries
    pub noexec: bool,
    /// Disable set-user-ID and set-group-ID bits
    pub nosuid: bool,
    /// Disable device file access
    pub nodev: bool,
}

impl Default for MountFlags {
    fn default() -> Self {
        Self {
            readonly: false,
            noexec: false,
            nosuid: false,
            nodev: false,
        }
    }
}

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
}

/// Global mount ID counter
static NEXT_MOUNT_ID: AtomicUsize = AtomicUsize::new(1);

impl MountPoint {
    /// Create a new mount point
    pub fn new(path: String, source: String, fs_type: String, flags: MountFlags) -> Self {
        let mount_id = NEXT_MOUNT_ID.fetch_add(1, Ordering::SeqCst);
        Self {
            path,
            source,
            fs_type,
            flags,
            mount_id,
            block_device: None,
        }
    }
    
    /// Create a new mount point with a block device
    pub fn new_with_device(
        path: String, 
        source: String, 
        fs_type: String, 
        flags: MountFlags,
        device: Arc<dyn BlockDevice>
    ) -> Self {
        let mount_id = NEXT_MOUNT_ID.fetch_add(1, Ordering::SeqCst);
        Self {
            path,
            source,
            fs_type,
            flags,
            mount_id,
            block_device: Some(device),
        }
    }
}

/// Basic mount table structure
pub struct MountTable {
    /// List of all mount points
    mounts: Vec<MountPoint>,
}

impl MountTable {
    /// Create a new empty mount table
    pub const fn new() -> Self {
        Self {
            mounts: Vec::new(),
        }
    }

    /// Add a new mount point to the table
    pub fn mount(&mut self, mount_point: MountPoint) -> Result<(), &'static str> {
        // Check for duplicate mount paths
        if self.mounts.iter().any(|m| m.path == mount_point.path) {
            return Err("Mount point already exists");
        }

        self.mounts.push(mount_point);
        Ok(())
    }

    /// Remove a mount point by path
    pub fn unmount(&mut self, path: &str) -> Result<(), &'static str> {
        let original_len = self.mounts.len();
        self.mounts.retain(|m| m.path != path);
        
        if self.mounts.len() == original_len {
            Err("Mount point not found")
        } else {
            Ok(())
        }
    }

    /// Find a mount point by path
    pub fn find_mount(&self, path: &str) -> Option<&MountPoint> {
        // Find the longest matching mount path
        self.mounts
            .iter()
            .filter(|m| path.starts_with(&m.path))
            .max_by_key(|m| m.path.len())
    }

    /// Get all mount points
    pub fn get_all_mounts(&self) -> &[MountPoint] {
        &self.mounts
    }

    /// Get mount information for a path
    pub fn get_mount_info(&self, path: &str) -> Option<MountInfo> {
        self.find_mount(path).map(|m| MountInfo {
            mount_path: m.path.clone(),
            fs_type: m.fs_type.clone(),
            flags: m.flags,
            mount_id: m.mount_id,
        })
    }
}

/// Simplified mount information
#[derive(Debug, Clone)]
pub struct MountInfo {
    /// The mount path
    pub mount_path: String,
    /// The filesystem type
    pub fs_type: String,
    /// Mount flags
    pub flags: MountFlags,
    /// Mount ID
    pub mount_id: usize,
}

// Global mount table instance
static mut GLOBAL_MOUNT_TABLE: Option<MountTable> = None;
static MOUNT_TABLE_INIT: AtomicUsize = AtomicUsize::new(0);

/// Initialize the global mount table
pub fn init_mount_table() {
    if MOUNT_TABLE_INIT.fetch_add(1, Ordering::SeqCst) == 0 {
        unsafe {
            GLOBAL_MOUNT_TABLE = Some(MountTable::new());
        }
    }
}

/// Get a reference to the global mount table
pub fn with_mount_table<F, R>(f: F) -> Option<R>
where
    F: FnOnce(&MountTable) -> R,
{
    unsafe {
        GLOBAL_MOUNT_TABLE.as_ref().map(f)
    }
}

/// Get a mutable reference to the global mount table
pub fn with_mount_table_mut<F, R>(f: F) -> Option<R>
where
    F: FnOnce(&mut MountTable) -> R,
{
    unsafe {
        GLOBAL_MOUNT_TABLE.as_mut().map(f)
    }
}

/// Convenience function to get mount info for a path
pub fn get_mount_info(path: &str) -> Option<MountInfo> {
    with_mount_table(|table| table.get_mount_info(path)).flatten()
}

/// Resolve a path to its mount point and relative path
pub fn resolve_mount_path(path: &str) -> Option<(MountPoint, String)> {
    with_mount_table(|table| {
        table.find_mount(path).map(|mount| {
            let mount_path = &mount.path;
            let relative_path = if path.starts_with(mount_path) {
                let relative = &path[mount_path.len()..];
                if relative.is_empty() {
                    "/".to_string()
                } else if relative.starts_with('/') {
                    relative.to_string()
                } else {
                    format!("/{}", relative)
                }
            } else {
                "/".to_string()
            };
            (mount.clone(), relative_path)
        })
    }).flatten()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_mount_table_basic() {
        let mut table = MountTable::new();
        
        let mount = MountPoint::new(
            "/mnt/data".into(),
            "/dev/sda1".into(),
            "ext4".into(),
            MountFlags::default(),
        );
        
        assert!(table.mount(mount).is_ok());
        assert!(table.find_mount("/mnt/data/file.txt").is_some());
        assert!(table.unmount("/mnt/data").is_ok());
        assert!(table.find_mount("/mnt/data/file.txt").is_none());
    }
}