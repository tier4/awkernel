pub mod error;
pub mod fat_vfs;
pub mod filesystem;
pub mod path;

use crate::{
    file::fatfs::{get_memory_fatfs, get_storage_fatfs, is_storage_fatfs_ready},
    sync::rwlock::RwLock,
};
use alloc::sync::Arc;
use fat_vfs::FatVfs;
use filesystem::VfsFileSystem;

// ── Global VFS singleton ──────────────────────────────────────────────────────

static VFS_INSTANCE: RwLock<Option<Arc<dyn VfsFileSystem>>> = RwLock::new(None);

/// Initialise the VFS from whichever FAT filesystem is already mounted.
///
/// Prefers the storage-backed FAT (virtio-blk / RAM disk) over the legacy
/// in-memory FAT.  Safe to call multiple times — only the first call takes
/// effect.
pub fn init_vfs() {
    let mut guard = VFS_INSTANCE.write();
    if guard.is_some() {
        return;
    }

    let vfs: Arc<dyn VfsFileSystem> = if is_storage_fatfs_ready() {
        Arc::new(FatVfs::new(get_storage_fatfs()))
    } else {
        Arc::new(FatVfs::new(get_memory_fatfs()))
    };

    *guard = Some(vfs);
    log::info!("VFS initialized.");
}

/// Returns `true` once `init_vfs()` has completed successfully.
pub fn is_vfs_ready() -> bool {
    VFS_INSTANCE.read().is_some()
}

/// Return a handle to the global VFS.
///
/// Panics if `init_vfs()` has not been called yet.
pub fn get_vfs() -> Arc<dyn VfsFileSystem> {
    VFS_INSTANCE
        .read()
        .clone()
        .expect("VFS not initialized — call init_vfs() first")
}
