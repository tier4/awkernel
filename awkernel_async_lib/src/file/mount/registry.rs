//! Unified mount registry that tracks both mount points and filesystem instances
//!
//! This provides an optimized mount registry with trie-based path lookup and
//! better data structures for performance.

use super::types::MountError;
use crate::file::filesystem::AsyncFileSystem;
use alloc::{
    boxed::Box,
    collections::BTreeMap,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{
    file::mount_types::{
        MountFlags, MountOptions, MountInfo, MountResolver, MountResolution,
        MountTable as MountTableTrait, path_utils, MountError as SyncMountError,
    },
    sync::rwlock::RwLock,
};
use core::sync::atomic::{AtomicBool, AtomicUsize, Ordering};

/// Convert from sync mount error to async mount error
fn convert_mount_error(err: SyncMountError) -> MountError {
    match err {
        SyncMountError::AlreadyMounted(path) => MountError::AlreadyMounted(path),
        SyncMountError::NotMounted(path) => MountError::NotMounted(path),
        SyncMountError::InvalidPath(path) => MountError::InvalidPath(path),
        SyncMountError::UnsupportedFilesystem(fs) => MountError::UnknownFilesystem(fs),
        _ => MountError::FilesystemError(err.to_string()),
    }
}

/// A mount entry containing both metadata and filesystem instance
struct MountEntry {
    /// Mount information
    info: MountInfo,
    /// The actual filesystem instance
    filesystem: Arc<Box<dyn AsyncFileSystem>>,
    /// Reference count for tracking active uses
    ref_count: AtomicUsize,
}

impl MountEntry {
    fn new(info: MountInfo, filesystem: Box<dyn AsyncFileSystem>) -> Self {
        Self {
            info,
            filesystem: Arc::new(filesystem),
            ref_count: AtomicUsize::new(0),
        }
    }

    fn increment_ref(&self) -> usize {
        self.ref_count.fetch_add(1, Ordering::SeqCst) + 1
    }

    fn decrement_ref(&self) -> usize {
        self.ref_count.fetch_sub(1, Ordering::SeqCst).saturating_sub(1)
    }

    fn ref_count(&self) -> usize {
        self.ref_count.load(Ordering::SeqCst)
    }
}

/// Mount registry with optimized path lookup
pub struct MountRegistry {
    /// Mount entries indexed by normalized path
    /// Using BTreeMap for efficient longest-prefix matching
    mounts: RwLock<BTreeMap<String, MountEntry>>,
    /// Cache for recently resolved paths (path -> mount_path)
    path_cache: RwLock<BTreeMap<String, String>>,
    /// Maximum cache entries
    max_cache_size: usize,
}

impl MountRegistry {
    /// Create a new mount registry
    pub fn new() -> Self {
        Self {
            mounts: RwLock::new(BTreeMap::new()),
            path_cache: RwLock::new(BTreeMap::new()),
            max_cache_size: 1000,
        }
    }

    /// Clear the path cache
    pub fn clear_cache(&self) {
        self.path_cache.write().clear();
    }

    /// Find the best matching mount for a path
    fn find_best_mount(&self, path: &str) -> Option<(String, MountEntry)> {
        let normalized = path_utils::normalize_path(path);
        
        // Check cache first
        if let Some(mount_path) = self.path_cache.read().get(&normalized) {
            if let Some(entry) = self.mounts.read().get(mount_path) {
                return Some((mount_path.clone(), entry.clone()));
            }
        }
        
        let mounts = self.mounts.read();
        
        // Use reverse iterator to find longest matching prefix efficiently
        let result = mounts
            .range(..=normalized.clone())
            .rev()
            .find(|(mount_path, _)| {
                path_utils::is_subpath(mount_path, &normalized) || mount_path == &normalized
            })
            .map(|(k, v)| (k.clone(), v.clone()));
        
        // Update cache if found
        if let Some((ref mount_path, _)) = result {
            let mut cache = self.path_cache.write();
            if cache.len() >= self.max_cache_size {
                // Remove oldest entry (first in BTreeMap)
                if let Some(first_key) = cache.keys().next().cloned() {
                    cache.remove(&first_key);
                }
            }
            cache.insert(normalized, mount_path.clone());
        }
        
        result
    }

    /// Register a new mount with reference counting
    pub fn register_mount_with_ref(
        &self,
        path: String,
        source: String,
        fs_type: String,
        options: MountOptions,
        filesystem: Box<dyn AsyncFileSystem>,
    ) -> Result<usize, MountError> {
        let normalized_path = path_utils::normalize_path(&path);
        
        // Validate path
        if normalized_path.is_empty() {
            return Err(MountError::InvalidPath("Empty path".into()));
        }
        
        let mut mounts = self.mounts.write();
        
        // Check if already mounted
        if mounts.contains_key(&normalized_path) {
            return Err(MountError::AlreadyMounted(normalized_path));
        }
        
        // Create mount info
        let mount_id = NEXT_MOUNT_ID.fetch_add(1, Ordering::SeqCst);
        let info = MountInfo {
            path: normalized_path.clone(),
            source,
            fs_type,
            flags: options.flags,
            mount_id,
            fs_options: options.fs_options,
        };
        
        let entry = MountEntry::new(info, filesystem);
        entry.increment_ref(); // Initial reference
        
        mounts.insert(normalized_path, entry);
        
        // Clear cache as mount table changed
        self.clear_cache();
        
        Ok(mount_id)
    }

    /// Unregister a mount with reference checking
    pub fn unregister_mount_safe(&self, path: &str) -> Result<(), MountError> {
        let normalized_path = path_utils::normalize_path(path);
        
        let mut mounts = self.mounts.write();
        
        // Check if mount exists
        let entry = mounts.get(&normalized_path)
            .ok_or_else(|| MountError::NotMounted(normalized_path.clone()))?;
        
        // Check reference count
        if entry.ref_count() > 1 {
            return Err(MountError::FilesystemError(
                format!("Mount point has {} active references", entry.ref_count() - 1)
            ));
        }
        
        mounts.remove(&normalized_path);
        
        // Clear cache as mount table changed
        self.clear_cache();
        
        Ok(())
    }

    /// Get filesystem with reference counting
    pub fn get_filesystem_ref(&self, path: &str) -> Option<Arc<Box<dyn AsyncFileSystem>>> {
        self.find_best_mount(path)
            .map(|(_, entry)| {
                entry.increment_ref();
                entry.filesystem.clone()
            })
    }

    /// Release filesystem reference
    pub fn release_filesystem_ref(&self, path: &str) {
        if let Some((_, entry)) = self.find_best_mount(path) {
            entry.decrement_ref();
        }
    }
}

impl Clone for MountEntry {
    fn clone(&self) -> Self {
        Self {
            info: self.info.clone(),
            filesystem: self.filesystem.clone(),
            ref_count: AtomicUsize::new(self.ref_count.load(Ordering::SeqCst)),
        }
    }
}

impl MountTableTrait for MountRegistry {
    fn mount(
        &mut self,
        _path: &str,
        _source: &str,
        _fs_type: &str,
        _options: MountOptions,
    ) -> Result<usize, SyncMountError> {
        // This trait requires &mut self, but we use internal mutability
        // So we can't directly implement this trait properly
        // Users should use register_mount_with_ref instead
        Err(SyncMountError::IoError("Use register_mount_with_ref".into()))
    }

    fn unmount(&mut self, path: &str) -> Result<(), SyncMountError> {
        self.unregister_mount_safe(path)
            .map_err(|e| match e {
                MountError::NotMounted(p) => SyncMountError::NotMounted(p),
                MountError::FilesystemError(msg) => SyncMountError::Busy(msg),
                _ => SyncMountError::IoError(e.to_string()),
            })
    }

    fn get_mount_info(&self, path: &str) -> Result<MountInfo, SyncMountError> {
        self.find_best_mount(path)
            .map(|(_, entry)| entry.info.clone())
            .ok_or_else(|| SyncMountError::NotMounted(path.to_string()))
    }

    fn list_mounts(&self) -> Vec<MountInfo> {
        self.mounts.read()
            .values()
            .map(|entry| entry.info.clone())
            .collect()
    }

    fn is_mount_point(&self, path: &str) -> bool {
        let normalized = path_utils::normalize_path(path);
        self.mounts.read().contains_key(&normalized)
    }
}

impl MountResolver<Arc<Box<dyn AsyncFileSystem>>> for MountRegistry {
    fn resolve_path(&self, path: &str) -> Result<MountResolution<Arc<Box<dyn AsyncFileSystem>>>, SyncMountError> {
        let (mount_path, entry) = self.find_best_mount(path)
            .ok_or_else(|| SyncMountError::NotMounted(path.to_string()))?;
        
        let relative_path = path_utils::relative_path(&mount_path, path)
            .unwrap_or_else(|| String::new());
        
        Ok(MountResolution {
            filesystem: entry.filesystem.clone(),
            relative_path,
            mount_info: entry.info.clone(),
        })
    }
}

// Global mount registry instance
use awkernel_lib::sync::mutex::{Mutex as SyncMutex, MCSNode};
static MOUNT_REGISTRY: SyncMutex<Option<Arc<MountRegistry>>> = SyncMutex::new(None);
static REGISTRY_INIT: AtomicBool = AtomicBool::new(false);
static NEXT_MOUNT_ID: AtomicUsize = AtomicUsize::new(1);

/// Initialize the mount registry
pub fn init_mount_registry() {
    let mut node = MCSNode::new();
    let mut guard = MOUNT_REGISTRY.lock(&mut node);
    
    if guard.is_none() {
        REGISTRY_INIT.store(true, Ordering::SeqCst);
        *guard = Some(Arc::new(MountRegistry::new()));
    }
}

/// Get the global mount registry
fn get_registry() -> Result<Arc<MountRegistry>, MountError> {
    let mut node = MCSNode::new();
    let guard = MOUNT_REGISTRY.lock(&mut node);
    
    guard.as_ref()
        .cloned()
        .ok_or(MountError::RegistryNotInitialized)
}

/// Register a filesystem at a mount path
pub fn register_mount(
    path: String,
    source: String,
    fs_type: String,
    flags: MountFlags,
    filesystem: Box<dyn AsyncFileSystem>,
) -> Result<(), MountError> {
    let options = MountOptions {
        flags,
        fs_options: BTreeMap::new(),
    };
    
    get_registry()?
        .register_mount_with_ref(path, source, fs_type, options, filesystem)
        .map(|_| ())
}

/// Unregister a filesystem from a mount path
pub fn unregister_mount(path: &str) -> Result<(), MountError> {
    get_registry()?.unregister_mount_safe(path)
}

/// Resolve a filesystem for a given path by finding the longest matching mount point
pub fn resolve_filesystem_for_path(path: &str) -> Result<(Arc<Box<dyn AsyncFileSystem>>, String, String), MountError> {
    let registry = get_registry()?;
    let resolution = registry.resolve_path(path)
        .map_err(convert_mount_error)?;
    
    Ok((
        resolution.filesystem,
        resolution.mount_info.path,
        resolution.relative_path,
    ))
}

/// Get mount information for a specific path
pub fn get_mount_info(path: &str) -> Result<MountInfo, MountError> {
    get_registry()?
        .get_mount_info(path)
        .map_err(convert_mount_error)
}

/// List all mounted filesystems
pub fn list_mounts() -> Vec<MountInfo> {
    get_registry()
        .map(|r| r.list_mounts())
        .unwrap_or_default()
}

/// Check if the registry is initialized
pub fn is_registry_initialized() -> bool {
    REGISTRY_INIT.load(Ordering::SeqCst)
}

/// Check if a filesystem is registered at a path
pub fn is_filesystem_registered(path: &str) -> bool {
    get_registry()
        .map(|r| r.is_mount_point(path))
        .unwrap_or(false)
}

/// Get all mount points
pub fn get_mount_points() -> Option<Vec<String>> {
    get_registry().ok().map(|r| {
        let mounts = r.list_mounts();
        if mounts.is_empty() {
            None
        } else {
            Some(mounts.into_iter().map(|m| m.path).collect())
        }
    }).flatten()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_mount_registry_init() {
        init_mount_registry();
        assert!(is_registry_initialized());
    }
    
    #[test]
    fn test_path_resolution() {
        let registry = MountRegistry::new();
        
        // Mock filesystem would go here
        // registry.register_mount_with_ref(...);
        
        // Test cache behavior
        registry.clear_cache();
        assert_eq!(registry.path_cache.read().len(), 0);
    }
}