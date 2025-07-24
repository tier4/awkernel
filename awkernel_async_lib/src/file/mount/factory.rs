//! Filesystem factory implementations
//!
//! This module provides the factory pattern for creating filesystem instances.

use super::types::{MountError, MountOptions, MountResult};
use crate::file::{
    filesystem::AsyncFileSystem,
    fatfs::AsyncFatFs,
};
use alloc::{
    boxed::Box,
    string::{String, ToString},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::{
    allocator::System,
    file::{
        block_device::BlockDevice,
        fatfs::create_fatfs_from_block_device,
        memfs::MemoryBlockDevice,
    },
    paging::PAGESIZE,
};
use core::{
    alloc::{GlobalAlloc, Layout},
};

/// Default size for memory filesystems (1MB)
const DEFAULT_MEMORY_FS_SIZE: usize = 1024 * 1024;

/// Default block size for memory filesystems
const DEFAULT_BLOCK_SIZE: usize = 512;

/// Trait for async filesystem factories
#[async_trait::async_trait]
pub trait AsyncFileSystemFactory: Send + Sync {
    /// Create a new filesystem instance
    async fn create(
        &self,
        device: Option<Arc<dyn BlockDevice>>,
        options: &MountOptions,
    ) -> MountResult<Box<dyn AsyncFileSystem>>;
    
    /// Get the filesystem type name
    fn fs_type(&self) -> &str;
}

/// FatFs filesystem factory
pub struct FatFsFactory;

#[async_trait::async_trait]
impl AsyncFileSystemFactory for FatFsFactory {
    async fn create(
        &self,
        device: Option<Arc<dyn BlockDevice>>,
        options: &MountOptions,
    ) -> MountResult<Box<dyn AsyncFileSystem>> {
        // For now, we only support memory-backed FatFs
        // Device parameter is ignored, we always create a memory device
        let _ = device;
        
        // Get size from options
        use crate::file::mount::types::mount_options_ext;
        let size = mount_options_ext::get_size(options)
            .unwrap_or(DEFAULT_MEMORY_FS_SIZE);
        
        // Check if we should format the filesystem
        let format = mount_options_ext::get_format(options)
            .unwrap_or(true); // Default to formatting new filesystems
        
        // Create a memory block device
        let memory_device = create_memory_block_device_concrete(size)?;
        
        // Create the FatFs filesystem
        let fs = create_fatfs_from_block_device(memory_device, format)
            .map_err(|e| MountError::FilesystemError(e))?;
        
        // Wrap in AsyncFatFs - construct directly
        let async_fs = AsyncFatFs {
            fs: Arc::new(fs),
        };
        
        Ok(Box::new(async_fs))
    }
    
    fn fs_type(&self) -> &str {
        "fatfs"
    }
}


/// Create a memory block device with the specified size (returns concrete type)
fn create_memory_block_device_concrete(size: usize) -> MountResult<Arc<MemoryBlockDevice>> {
    // Allocate memory using System allocator for proper alignment
    let disk_layout = Layout::from_size_align(size, PAGESIZE)
        .map_err(|_| MountError::FilesystemError("Invalid layout for memory filesystem".into()))?;
    
    let raw_memory = unsafe { System.alloc(disk_layout) };
    if raw_memory.is_null() {
        return Err(MountError::FilesystemError("Failed to allocate memory for filesystem".into()));
    }
    
    // Create a Vec from the allocated memory
    let disk_data = unsafe {
        Vec::from_raw_parts(raw_memory, size, size)
    };
    
    // Create a MemoryBlockDevice
    let memory_device = Arc::new(MemoryBlockDevice::from_vec(disk_data, DEFAULT_BLOCK_SIZE));
    
    Ok(memory_device)
}

/// Global registry of filesystem factories
static mut FS_FACTORIES: Option<BTreeMap<String, Box<dyn AsyncFileSystemFactory>>> = None;
static FS_FACTORIES_INIT: core::sync::atomic::AtomicBool = 
    core::sync::atomic::AtomicBool::new(false);

use alloc::collections::BTreeMap;
use core::sync::atomic::Ordering;

/// Initialize the filesystem factory registry
fn init_fs_factories() {
    if !FS_FACTORIES_INIT.swap(true, Ordering::SeqCst) {
        unsafe {
            FS_FACTORIES = Some(BTreeMap::new());
        }
    }
}

/// Register a filesystem factory
pub fn register_filesystem_factory(factory: Box<dyn AsyncFileSystemFactory>) -> MountResult<()> {
    init_fs_factories();
    
    unsafe {
        if let Some(factories) = FS_FACTORIES.as_mut() {
            let fs_type = factory.fs_type().to_string();
            factories.insert(fs_type, factory);
            Ok(())
        } else {
            Err(MountError::RegistryNotInitialized)
        }
    }
}

/// Get a filesystem factory by type
pub fn get_filesystem_factory(fs_type: &str) -> MountResult<&'static dyn AsyncFileSystemFactory> {
    unsafe {
        FS_FACTORIES.as_ref()
            .and_then(|f| f.get(fs_type))
            .map(|f| f.as_ref())
            .ok_or_else(|| MountError::FactoryNotFound(fs_type.to_string()))
    }
}

/// Initialize default filesystem factories
pub fn init_default_factories() {
    init_fs_factories();
    let _ = register_filesystem_factory(Box::new(FatFsFactory));
}