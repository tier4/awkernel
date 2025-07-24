//! Mount lifecycle management with tracking of open files and resources
//!
//! This module provides safe mount/unmount operations by tracking active resources.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;
use alloc::sync::{Arc, Weak};
use alloc::format;
use awkernel_sync::rwlock::RwLock;
use core::sync::atomic::{AtomicUsize, Ordering};
use super::mount_types::{MountError, MountInfo};

/// Unique identifier for open file handles
pub type FileHandleId = usize;

/// Tracks lifecycle of a mounted filesystem
pub struct MountLifecycle {
    /// Open file handles on this mount
    open_files: RwLock<BTreeSet<FileHandleId>>,
    /// Active operations counter
    active_ops: AtomicUsize,
    /// Mount information
    mount_info: RwLock<Option<MountInfo>>,
}

impl Default for MountLifecycle {
    fn default() -> Self {
        Self {
            open_files: RwLock::new(BTreeSet::new()),
            active_ops: AtomicUsize::new(0),
            mount_info: RwLock::new(None),
        }
    }
}

impl MountLifecycle {
    /// Create a new mount lifecycle tracker
    pub fn new(mount_info: MountInfo) -> Self {
        Self {
            open_files: RwLock::new(BTreeSet::new()),
            active_ops: AtomicUsize::new(0),
            mount_info: RwLock::new(Some(mount_info)),
        }
    }

    /// Register an open file handle
    pub fn register_file(&self, handle_id: FileHandleId) {
        self.open_files.write().insert(handle_id);
    }

    /// Unregister a closed file handle
    pub fn unregister_file(&self, handle_id: FileHandleId) {
        self.open_files.write().remove(&handle_id);
    }

    /// Begin an operation on this mount
    pub fn begin_operation(&self) -> OperationGuard {
        self.active_ops.fetch_add(1, Ordering::SeqCst);
        OperationGuard { lifecycle: self }
    }

    /// Check if mount can be safely unmounted
    pub fn can_unmount(&self) -> Result<(), MountError> {
        let open_count = self.open_files.read().len();
        if open_count > 0 {
            return Err(MountError::Busy(
                format!("Mount has {} open files", open_count)
            ));
        }

        let active_ops = self.active_ops.load(Ordering::SeqCst);
        if active_ops > 0 {
            return Err(MountError::Busy(
                format!("Mount has {} active operations", active_ops)
            ));
        }

        Ok(())
    }

    /// Get number of open files
    pub fn open_file_count(&self) -> usize {
        self.open_files.read().len()
    }

    /// Get number of active operations
    pub fn active_operation_count(&self) -> usize {
        self.active_ops.load(Ordering::SeqCst)
    }

    /// Get mount information
    pub fn mount_info(&self) -> Option<MountInfo> {
        self.mount_info.read().clone()
    }
}

/// Guard that automatically decrements active operations on drop
pub struct OperationGuard<'a> {
    lifecycle: &'a MountLifecycle,
}

impl<'a> Drop for OperationGuard<'a> {
    fn drop(&mut self) {
        self.lifecycle.active_ops.fetch_sub(1, Ordering::SeqCst);
    }
}

/// Global mount lifecycle manager
pub struct MountLifecycleManager {
    /// Map of mount paths to lifecycle trackers
    mounts: RwLock<BTreeMap<String, Arc<MountLifecycle>>>,
    /// Next file handle ID
    next_handle_id: AtomicUsize,
}

impl MountLifecycleManager {
    /// Create a new lifecycle manager
    pub const fn new() -> Self {
        Self {
            mounts: RwLock::new(BTreeMap::new()),
            next_handle_id: AtomicUsize::new(1),
        }
    }

    /// Register a new mount
    pub fn register_mount(&self, mount_info: MountInfo) -> Arc<MountLifecycle> {
        let lifecycle = Arc::new(MountLifecycle::new(mount_info.clone()));
        self.mounts.write().insert(mount_info.path, lifecycle.clone());
        lifecycle
    }

    /// Unregister a mount (if safe)
    pub fn unregister_mount(&self, path: &str) -> Result<(), MountError> {
        let mounts = self.mounts.read();
        
        if let Some(lifecycle) = mounts.get(path) {
            lifecycle.can_unmount()?;
        } else {
            return Err(MountError::NotMounted(path.into()));
        }
        
        drop(mounts);
        self.mounts.write().remove(path);
        Ok(())
    }

    /// Get lifecycle for a mount
    pub fn get_mount_lifecycle(&self, path: &str) -> Option<Arc<MountLifecycle>> {
        self.mounts.read().get(path).cloned()
    }

    /// Generate a new file handle ID
    pub fn new_file_handle(&self) -> FileHandleId {
        self.next_handle_id.fetch_add(1, Ordering::SeqCst)
    }

    /// Get mount statistics
    pub fn get_mount_stats(&self, path: &str) -> Option<MountStats> {
        self.mounts.read().get(path).map(|lifecycle| {
            MountStats {
                path: path.into(),
                open_files: lifecycle.open_file_count(),
                active_operations: lifecycle.active_operation_count(),
            }
        })
    }

    /// List all mount statistics
    pub fn list_mount_stats(&self) -> Vec<MountStats> {
        self.mounts.read()
            .iter()
            .map(|(path, lifecycle)| MountStats {
                path: path.clone(),
                open_files: lifecycle.open_file_count(),
                active_operations: lifecycle.active_operation_count(),
            })
            .collect()
    }

    /// Force unmount (closes all files)
    pub fn force_unmount(&self, path: &str) -> Result<Vec<FileHandleId>, MountError> {
        let mut mounts = self.mounts.write();
        
        let lifecycle = mounts.get(path)
            .ok_or_else(|| MountError::NotMounted(path.into()))?;
        
        // Collect all open file handles
        let open_files: Vec<_> = lifecycle.open_files.read().iter().copied().collect();
        
        // Remove the mount
        mounts.remove(path);
        
        Ok(open_files)
    }
}

/// Statistics for a mounted filesystem
#[derive(Debug, Clone)]
pub struct MountStats {
    /// Mount path
    pub path: String,
    /// Number of open files
    pub open_files: usize,
    /// Number of active operations
    pub active_operations: usize,
}

/// File handle that automatically tracks its lifecycle
pub struct TrackedFileHandle {
    /// The file handle ID
    pub id: FileHandleId,
    /// Weak reference to the mount lifecycle
    lifecycle: Weak<MountLifecycle>,
}

impl TrackedFileHandle {
    /// Create a new tracked file handle
    pub fn new(manager: &MountLifecycleManager, mount_path: &str) -> Option<Self> {
        let lifecycle = manager.get_mount_lifecycle(mount_path)?;
        let id = manager.new_file_handle();
        
        lifecycle.register_file(id);
        
        Some(Self {
            id,
            lifecycle: Arc::downgrade(&lifecycle),
        })
    }
}

impl Drop for TrackedFileHandle {
    fn drop(&mut self) {
        if let Some(lifecycle) = self.lifecycle.upgrade() {
            lifecycle.unregister_file(self.id);
        }
    }
}

// Global lifecycle manager instance
use awkernel_sync::mutex::{Mutex, MCSNode};
static LIFECYCLE_MANAGER: Mutex<Option<Arc<MountLifecycleManager>>> = Mutex::new(None);

/// Get the global lifecycle manager
pub fn get_lifecycle_manager() -> Arc<MountLifecycleManager> {
    let mut node = MCSNode::new();
    let mut guard = LIFECYCLE_MANAGER.lock(&mut node);
    
    if guard.is_none() {
        *guard = Some(Arc::new(MountLifecycleManager::new()));
    }
    
    guard.clone().unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::file::mount_types::MountFlags;

    #[test]
    fn test_mount_lifecycle() {
        let manager = MountLifecycleManager::new();
        
        let mount_info = MountInfo {
            path: "/test".into(),
            source: "/dev/test".into(),
            fs_type: "testfs".into(),
            flags: MountFlags::new(),
            mount_id: 1,
            fs_options: BTreeMap::new(),
        };
        
        let lifecycle = manager.register_mount(mount_info);
        
        // Should be able to unmount when no files open
        assert!(lifecycle.can_unmount().is_ok());
        
        // Register a file
        let handle_id = manager.new_file_handle();
        lifecycle.register_file(handle_id);
        
        // Should not be able to unmount with open file
        assert!(lifecycle.can_unmount().is_err());
        
        // Unregister the file
        lifecycle.unregister_file(handle_id);
        
        // Should be able to unmount again
        assert!(lifecycle.can_unmount().is_ok());
    }

    #[test]
    fn test_active_operations() {
        let mount_info = MountInfo {
            path: "/test".into(),
            source: "/dev/test".into(),
            fs_type: "testfs".into(),
            flags: MountFlags::new(),
            mount_id: 1,
            fs_options: BTreeMap::new(),
        };
        
        let lifecycle = MountLifecycle::new(mount_info);
        
        // Should be able to unmount initially
        assert!(lifecycle.can_unmount().is_ok());
        
        // Begin an operation
        let _guard = lifecycle.begin_operation();
        
        // Should not be able to unmount with active operation
        assert!(lifecycle.can_unmount().is_err());
        assert_eq!(lifecycle.active_operation_count(), 1);
        
        // Drop the guard
        drop(_guard);
        
        // Should be able to unmount again
        assert!(lifecycle.can_unmount().is_ok());
        assert_eq!(lifecycle.active_operation_count(), 0);
    }

    #[test] 
    fn test_tracked_file_handle() {
        let manager = Arc::new(MountLifecycleManager::new());
        
        let mount_info = MountInfo {
            path: "/test".into(),
            source: "/dev/test".into(),
            fs_type: "testfs".into(),
            flags: MountFlags::new(),
            mount_id: 1,
            fs_options: BTreeMap::new(),
        };
        
        manager.register_mount(mount_info);
        
        // Create tracked handle
        {
            let _handle = TrackedFileHandle::new(&manager, "/test").unwrap();
            assert_eq!(manager.get_mount_stats("/test").unwrap().open_files, 1);
        }
        
        // Handle dropped, should be unregistered
        assert_eq!(manager.get_mount_stats("/test").unwrap().open_files, 0);
    }
}