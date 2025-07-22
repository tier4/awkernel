#![no_std]

extern crate alloc;

use alloc::string::ToString;
use alloc::sync::Arc;
use alloc::vec::Vec;
use awkernel_lib::file::mount::{
    MountFlags, MountPoint, init_mount_table, with_mount_table, 
    with_mount_table_mut, get_mount_info, resolve_mount_path
};
use awkernel_lib::file::block_device::{BlockDevice, MemoryBlockDevice};
use awkernel_lib::file::mount_manager::{
    MountManager, MountOptions, MountError, FileSystemFactory, 
    register_filesystem, mount_root
};
// Mount-aware paths will be tested when implemented
// use awkernel_lib::file::vfs::mount_aware::MountAwarePath;
// use awkernel_async_lib::file::path::AsyncVfsPath;
use awkernel_lib::delay::wait_millisec;
use log::{info, warn, error};

async fn test_basic_mount_operations() {
    info!("=== Testing Basic Mount Operations ===");
    
    init_mount_table();
    
    let result = with_mount_table_mut(|table| {
        let root_mount = MountPoint::new(
            "/".to_string(),
            "rootfs".to_string(),
            "memfs".to_string(),
            MountFlags::default(),
        );
        table.mount(root_mount)
    });
    
    match result {
        Some(Ok(())) => info!("✓ Root filesystem mounted successfully"),
        Some(Err(e)) => error!("✗ Failed to mount root: {}", e),
        None => error!("✗ Mount table not initialized"),
    }
    
    let result = with_mount_table_mut(|table| {
        let mut flags = MountFlags::default();
        flags.readonly = true;
        let rom_mount = MountPoint::new(
            "/rom".to_string(),
            "romfs".to_string(),
            "romfs".to_string(),
            flags,
        );
        table.mount(rom_mount)
    });
    
    match result {
        Some(Ok(())) => info!("✓ ROM filesystem mounted as readonly"),
        Some(Err(e)) => error!("✗ Failed to mount /rom: {}", e),
        None => error!("✗ Mount table not initialized"),
    }
    
    let result = with_mount_table_mut(|table| {
        let data_mount = MountPoint::new(
            "/data".to_string(),
            "/dev/sda1".to_string(),
            "ext4".to_string(),
            MountFlags::default(),
        );
        table.mount(data_mount)
    });
    
    match result {
        Some(Ok(())) => info!("✓ Data filesystem mounted"),
        Some(Err(e)) => error!("✗ Failed to mount /data: {}", e),
        None => error!("✗ Mount table not initialized"),
    }
    
    let duplicate_result = with_mount_table_mut(|table| {
        let dup_mount = MountPoint::new(
            "/data".to_string(),
            "/dev/sdb1".to_string(),
            "ext4".to_string(),
            MountFlags::default(),
        );
        table.mount(dup_mount)
    });
    
    match duplicate_result {
        Some(Err(_)) => info!("✓ Duplicate mount correctly rejected"),
        Some(Ok(())) => error!("✗ Duplicate mount should have failed"),
        None => error!("✗ Mount table not initialized"),
    }
    
    info!("\n=== Current Mount Table ===");
    if let Some(mounts) = with_mount_table(|table| {
        table.get_all_mounts().iter().map(|m| {
            (m.path.clone(), m.fs_type.clone(), m.flags.readonly, m.mount_id)
        }).collect::<Vec<_>>()
    }) {
        for (path, fs_type, readonly, id) in mounts {
            info!("Mount #{}: {} [{}] readonly={}", id, path, fs_type, readonly);
        }
    }
}

async fn test_path_resolution() {
    info!("\n=== Testing Path Resolution ===");
    
    let test_paths = [
        "/",
        "/rom/boot/kernel.img",
        "/data/users/alice/documents",
        "/tmp/cache",
        "/data",
    ];
    
    for path in &test_paths {
        if let Some(mount_info) = get_mount_info(path) {
            info!("Path '{}' -> Mount: {} [{}] readonly={}", 
                  path, mount_info.mount_path, mount_info.fs_type, mount_info.flags.readonly);
        } else {
            warn!("Path '{}' -> No mount found", path);
        }
    }
    
    info!("\n=== Testing Mount Path Resolution ===");
    for path in &test_paths {
        if let Some((mount, relative)) = resolve_mount_path(path) {
            info!("Path '{}' -> Mount: {} + Relative: '{}'", 
                  path, mount.path, relative);
        } else {
            warn!("Path '{}' -> Resolution failed", path);
        }
    }
    
    let unmount_result = with_mount_table_mut(|table| table.unmount("/data"));
    match unmount_result {
        Some(Ok(())) => info!("✓ Successfully unmounted /data"),
        Some(Err(e)) => error!("✗ Failed to unmount /data: {}", e),
        None => error!("✗ Mount table not initialized"),
    }
    
    if get_mount_info("/data/test").is_none() {
        info!("✓ /data paths no longer resolve after unmount");
    } else {
        error!("✗ /data paths still resolve after unmount");
    }
}

async fn test_block_device_mounts() {
    info!("\n=== Testing Block Device Mounts ===");
    
    // Create a memory block device with 512-byte blocks, 2048 blocks total (1MB)
    let mem_device = Arc::new(MemoryBlockDevice::new(512, 2048));
    info!("Created 1MB memory block device with {} byte blocks", 
          mem_device.block_size());
    
    let result = with_mount_table_mut(|table| {
        let mount = MountPoint::new_with_device(
            "/dev/mem0".to_string(),
            "memory0".to_string(),
            "ext4".to_string(),
            MountFlags::default(),
            mem_device.clone(),
        );
        table.mount(mount)
    });
    
    match result {
        Some(Ok(())) => info!("✓ Block device mount successful"),
        Some(Err(e)) => error!("✗ Failed to mount block device: {}", e),
        None => error!("✗ Mount table not initialized"),
    }
    
    // Create a memory block device with 4096-byte blocks, 1024 blocks total (4MB)
    let large_device = Arc::new(MemoryBlockDevice::new(4096, 1024));
    info!("Created 4MB memory block device with {} byte blocks", 
          large_device.block_size());
    
    let result = with_mount_table_mut(|table| {
        let mount = MountPoint::new_with_device(
            "/dev/mem1".to_string(),
            "memory1".to_string(),
            "ext4".to_string(),
            MountFlags::default(),
            large_device,
        );
        table.mount(mount)
    });
    
    match result {
        Some(Ok(())) => info!("✓ Large block device mount successful"),
        Some(Err(e)) => error!("✗ Failed to mount large block device: {}", e),
        None => error!("✗ Mount table not initialized"),
    }
}

// Requires ver3 implementation
#[allow(dead_code)]
async fn test_mount_aware_paths() {
    info!("\n=== Testing Mount-Aware Paths ===");
    /*
    
    let paths_to_test = [
        "/rom/boot/../config/system.conf",
        "/data/./users/../logs/app.log",
        "/rom/../data/test",
    ];
    
    for path in &paths_to_test {
        let aware_path = MountAwarePath::new(path);
        info!("Path: {}", path);
        info!("  Normalized: {}", aware_path.as_str());
        
        if let Some((mount_path, relative)) = aware_path.resolve_mount() {
            info!("  Mount: {} + Relative: {}", mount_path, relative);
            info!("  Filesystem: {:?}", aware_path.filesystem_type());
            info!("  Read-only: {}", aware_path.is_read_only());
        } else {
            warn!("  No mount found");
        }
    }
    
    let path1 = MountAwarePath::new("/rom/boot");
    let path2 = path1.join("../config/test.conf");
    info!("\nJoin test: {} + {} = {}", 
          path1.as_str(), "../config/test.conf", path2.as_str());
    
    if !path1.crosses_mount_boundary(&path2) {
        info!("✓ Paths on same mount point");
    } else {
        error!("✗ Paths unexpectedly cross mount boundary");
    }
    
    let path3 = MountAwarePath::new("/rom");
    let path4 = MountAwarePath::new("/data");
    if path3.crosses_mount_boundary(&path4) {
        info!("✓ Cross-mount detection works");
    } else {
        error!("✗ Failed to detect mount boundary crossing");
    }
    */
}

async fn test_mount_manager() {
    info!("\n=== Testing Mount Manager ===");
    
    init_mount_table();
    MountManager::init();
    
    let result = mount_root();
    match result {
        Ok(()) => info!("✓ Root mounted via MountManager"),
        Err(e) => error!("✗ Failed to mount root: {:?}", e),
    }
    
    let options = MountOptions::new()
        .read_only(true)
        .no_exec(true)
        .with_option("noatime", "true");
    
    let result = MountManager::mount(
        "/boot",
        "bootfs",
        "memfs",
        None,
        options,
    );
    
    match result {
        Ok(()) => info!("✓ /boot mounted with custom options"),
        Err(e) => error!("✗ Failed to mount /boot: {:?}", e),
    }
    
    // Create a memory block device with 512-byte blocks, 4096 blocks total (2MB)
    let device = Arc::new(MemoryBlockDevice::new(512, 4096));
    let result = MountManager::mount(
        "/storage",
        "/dev/vda",
        "ext4",
        Some(device),
        MountOptions::default(),
    );
    
    match result {
        Ok(()) => info!("✓ /storage mounted with block device"),
        Err(e) => error!("✗ Failed to mount /storage: {:?}", e),
    }
    
    let result = MountManager::mount(
        "/unknown",
        "unknownfs",
        "unknownfs",
        None,
        MountOptions::default(),
    );
    
    match result {
        Err(MountError::UnknownFilesystem(_)) => {
            info!("✓ Unknown filesystem correctly rejected")
        }
        Ok(()) => error!("✗ Unknown filesystem should have failed"),
        Err(e) => error!("✗ Unexpected error: {:?}", e),
    }
    
    info!("\n=== All Mounts via MountManager ===");
    let mounts = MountManager::list_mounts();
    for mount in mounts {
        info!("Mount: {} [{}] source={} readonly={} has_device={}", 
              mount.path, mount.fs_type, mount.source, 
              mount.flags.readonly, mount.has_device);
    }
    
    let unmount_result = MountManager::unmount("/boot");
    match unmount_result {
        Ok(()) => info!("✓ Successfully unmounted /boot"),
        Err(e) => error!("✗ Failed to unmount /boot: {:?}", e),
    }
}

// Requires ver4 implementation
#[allow(dead_code)]
async fn test_async_vfs_paths() {
    info!("\n=== Testing Async VFS Paths ===");
    /*
    
    if let Some((mount_point, relative)) = resolve_mount_path("/rom/config") {
        match AsyncVfsPath::from_mount_path(mount_point, relative).await {
            Ok(path) => {
                info!("✓ Created async path: {}", path.as_str());
                
                if let Some(info) = path.mount_info().await {
                    info!("  Mount: {} [{}]", info.mount_path, info.fs_type);
                    info!("  Flags: readonly={} noexec={}", 
                          info.flags.readonly, info.flags.noexec);
                }
                
                if path.is_read_only_mount().await {
                    info!("✓ Correctly detected read-only mount");
                }
            }
            Err(e) => error!("✗ Failed to create async path: {:?}", e),
        }
    }
    
    if let Some((mp1, rel1)) = resolve_mount_path("/rom/test") {
        if let Some((mp2, rel2)) = resolve_mount_path("/data/test") {
            if let Ok(path1) = AsyncVfsPath::from_mount_path(mp1, rel1).await {
                if let Ok(path2) = AsyncVfsPath::from_mount_path(mp2, rel2).await {
                    if path1.crosses_mount_boundary(&path2).await {
                        info!("✓ Async mount boundary detection works");
                    } else {
                        error!("✗ Failed to detect async mount boundary");
                    }
                }
            }
        }
    }
    */
}

struct CustomFileSystemFactory;

impl FileSystemFactory for CustomFileSystemFactory {
    fn create(
        &self,
        _device: Option<Arc<dyn BlockDevice>>,
        options: &MountOptions,
    ) -> Result<(), MountError> {
        info!("CustomFS: Creating with options: {:?}", options.fs_options);
        Ok(())
    }
    
    fn fs_type(&self) -> &str {
        "customfs"
    }
}

async fn test_custom_filesystem() {
    info!("\n=== Testing Custom Filesystem Registration ===");
    
    let result = register_filesystem(alloc::boxed::Box::new(CustomFileSystemFactory));
    match result {
        Ok(()) => info!("✓ Custom filesystem registered"),
        Err(e) => error!("✗ Failed to register custom filesystem: {:?}", e),
    }
    
    let options = MountOptions::new()
        .with_option("compression", "lz4")
        .with_option("cache_size", "16MB");
    
    let result = MountManager::mount(
        "/custom",
        "customfs",
        "customfs",
        None,
        options,
    );
    
    match result {
        Ok(()) => info!("✓ Custom filesystem mounted successfully"),
        Err(e) => error!("✗ Failed to mount custom filesystem: {:?}", e),
    }
}

pub async fn run() {
    wait_millisec(1000);
    info!("Starting mount table tests...\n");
    
    test_basic_mount_operations().await;
    test_path_resolution().await;
    test_block_device_mounts().await;
    // test_mount_aware_paths().await;  // Requires ver3 implementation
    test_mount_manager().await;
    // test_async_vfs_paths().await;    // Requires ver4 implementation
    test_custom_filesystem().await;
    
    info!("\n=== Mount Table Tests Complete ===");
}