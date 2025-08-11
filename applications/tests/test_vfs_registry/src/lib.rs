#![no_std]
#![no_main]

extern crate alloc;

use alloc::{boxed::Box, string::ToString, vec::Vec};
use awkernel_async_lib::{
    executor::Executor,
    file::{
        mount::{mount, MountOptions},
        filesystem::AsyncSeekAndWrite,
        path::AsyncVfsPath,
    },
};
use awkernel_lib::{print, println, file::memfs::create_memory_block_device};

#[awkernel_lib::test]
fn test_vfs_registry_basic() {
    println!("Testing VFS Registry basic functionality...");
    
    let executor = Executor::spawn_executor(None, 512);
    
    executor.spawn_detached(async {
        // Initialize mount system
        println!("Mount manager initialized");
        
        // Mount a memory filesystem at root
        let root_device = create_memory_block_device(1024 * 1024, 512)
            .expect("Failed to create root memory block device");
        let mut root_options = MountOptions::new();
        root_options.fs_options.insert("format".into(), "true".into());
        mount(
            "/",
            "rootfs",
            "fatfs",
            root_device,
            root_options,
        ).expect("Failed to mount root filesystem");
        println!("Root filesystem mounted");
        
        // Check if registered
        assert!(is_filesystem_registered("/"));
        println!("Root filesystem is registered");
        
        // Get mount points
        let mount_points = get_mount_points().expect("Failed to get mount points");
        assert_eq!(mount_points.len(), 1);
        assert_eq!(mount_points[0], "/");
        println!("Mount points retrieved correctly");
    });
    
    executor.run_tasks_until_complete();
    println!("Basic VFS registry test passed!");
}

#[awkernel_lib::test]
fn test_mount_aware_path_operations() {
    println!("Testing mount-aware path operations...");
    
    let executor = Executor::spawn_executor(None, 512);
    
    executor.spawn_detached(async {
        // Initialize and mount filesystems
        
        // Mount multiple filesystems
        let root_device = create_memory_block_device(1024 * 1024, 512)
            .expect("Failed to create root device");
        let mut root_options = MountOptions::new();
        root_options.fs_options.insert("format".into(), "true".into());
        mount("/", "rootfs", "fatfs", root_device, root_options)
            .await.expect("Failed to mount root");
            
        let disk1_device = create_memory_block_device(512 * 1024, 512)
            .expect("Failed to create disk1 device");
        let mut disk1_options = MountOptions::new();
        disk1_options.fs_options.insert("format".into(), "true".into());
        mount("/mnt/disk1", "disk1", "fatfs", disk1_device, disk1_options)
            .await.expect("Failed to mount disk1");
            
        let disk2_device = create_memory_block_device(512 * 1024, 512)
            .expect("Failed to create disk2 device");
        let mut disk2_options = MountOptions::new();
        disk2_options.fs_options.insert("format".into(), "true".into());
        mount("/mnt/disk2", "disk2", "fatfs", disk2_device, disk2_options)
            .await.expect("Failed to mount disk2");
        
        println!("All filesystems mounted");
        
        // Test file operations on root
        let root_file = AsyncVfsPath::new("/test.txt");
        let mut writer = root_file.create_file().expect("Failed to create file");
        writer.write_all(b"Root file content").expect("Failed to write");
        writer.flush().expect("Failed to flush");
        drop(writer);
        
        assert!(root_file.exists().expect("Failed to check existence"));
        println!("Root file created successfully");
        
        // Test file operations on disk1
        let disk1_dir = AsyncVfsPath::new("/mnt/disk1/data");
        disk1_dir.create_dir().expect("Failed to create directory");
        
        let disk1_file = AsyncVfsPath::new("/mnt/disk1/data/file.txt");
        let mut writer = disk1_file.create_file().expect("Failed to create file");
        writer.write_all(b"Disk1 file content").expect("Failed to write");
        writer.flush().expect("Failed to flush");
        drop(writer);
        
        assert!(disk1_file.exists().expect("Failed to check existence"));
        println!("Disk1 file created successfully");
        
        // Test directory listing
        let disk1_data = AsyncVfsPath::new("/mnt/disk1/data");
        let entries = disk1_data.read_dir().expect("Failed to read directory");
        assert_eq!(entries.len(), 1);
        println!("Directory listing works correctly");
        
        // Test that files are isolated between filesystems
        let disk2_file = AsyncVfsPath::new("/mnt/disk2/data/file.txt");
        assert!(!disk2_file.exists().expect("Failed to check existence"));
        println!("Filesystem isolation verified");
    });
    
    executor.run_tasks_until_complete();
    println!("Mount-aware path operations test passed!");
}

#[awkernel_lib::test]
fn test_cross_filesystem_operations() {
    println!("Testing cross-filesystem operations...");
    
    let executor = Executor::spawn_executor(None, 512);
    
    executor.spawn_detached(async {
        // Initialize and mount filesystems
        
        let root_device = create_memory_block_device(1024 * 1024, 512)
            .expect("Failed to create root device");
        let mut root_options = MountOptions::new();
        root_options.fs_options.insert("format".into(), "true".into());
        mount("/", "rootfs", "fatfs", root_device, root_options)
            .await.expect("Failed to mount root");
            
        let backup_device = create_memory_block_device(512 * 1024, 512)
            .expect("Failed to create backup device");
        let mut backup_options = MountOptions::new();
        backup_options.fs_options.insert("format".into(), "true".into());
        mount("/backup", "backup", "fatfs", backup_device, backup_options)
            .await.expect("Failed to mount backup");
        
        // Create source file
        let src_file = AsyncVfsPath::new("/source.txt");
        let mut writer = src_file.create_file().expect("Failed to create source");
        writer.write_all(b"Source content for copy test").expect("Failed to write");
        writer.flush().expect("Failed to flush");
        drop(writer);
        
        // Copy to different filesystem
        let dest_file = AsyncVfsPath::new("/backup/copy.txt");
        src_file.copy_file(&dest_file).expect("Failed to copy file");
        
        // Verify copy
        assert!(dest_file.exists().expect("Failed to check existence"));
        
        // Read and verify content
        let mut reader = dest_file.open_file().expect("Failed to open file");
        let mut content = alloc::string::String::new();
        reader.read_to_string(&mut content).expect("Failed to read");
        assert_eq!(content, "Source content for copy test");
        
        println!("Cross-filesystem copy test passed!");
    });
    
    executor.run_tasks_until_complete();
    println!("Cross-filesystem operations test passed!");
}

#[awkernel_lib::test]
fn test_nested_mount_points() {
    println!("Testing nested mount points...");
    
    let executor = Executor::spawn_executor(None, 512);
    
    executor.spawn_detached(async {
        // Initialize and mount filesystems
        
        // Create nested mount structure
        let root_device = create_memory_block_device(1024 * 1024, 512)
            .expect("Failed to create root device");
        let mut root_options = MountOptions::new();
        root_options.fs_options.insert("format".into(), "true".into());
        mount("/", "rootfs", "fatfs", root_device, root_options)
            .await.expect("Failed to mount root");
            
        let mnt_device = create_memory_block_device(512 * 1024, 512)
            .expect("Failed to create mnt device");
        let mut mnt_options = MountOptions::new();
        mnt_options.fs_options.insert("format".into(), "true".into());
        mount("/mnt", "mnt", "fatfs", mnt_device, mnt_options)
            .await.expect("Failed to mount /mnt");
            
        let usb_device = create_memory_block_device(256 * 1024, 512)
            .expect("Failed to create usb device");
        let mut usb_options = MountOptions::new();
        usb_options.fs_options.insert("format".into(), "true".into());
        mount("/mnt/usb", "usb", "fatfs", usb_device, usb_options)
            .await.expect("Failed to mount /mnt/usb");
        
        // Create files at each level
        let root_file = AsyncVfsPath::new("/root.txt");
        let mut writer = root_file.create_file().expect("Failed to create root file");
        writer.write_all(b"Root").expect("Failed to write");
        drop(writer);
        
        let mnt_file = AsyncVfsPath::new("/mnt/mnt.txt");
        let mut writer = mnt_file.create_file().expect("Failed to create mnt file");
        writer.write_all(b"Mnt").expect("Failed to write");
        drop(writer);
        
        let usb_file = AsyncVfsPath::new("/mnt/usb/usb.txt");
        let mut writer = usb_file.create_file().expect("Failed to create usb file");
        writer.write_all(b"USB").expect("Failed to write");
        drop(writer);
        
        // Verify each file exists only in its filesystem
        assert!(root_file.exists().expect("Failed to check"));
        assert!(mnt_file.exists().expect("Failed to check"));
        assert!(usb_file.exists().expect("Failed to check"));
        
        // Verify files don't exist in wrong filesystems
        let wrong_path = AsyncVfsPath::new("/mnt.txt");
        assert!(!wrong_path.exists().expect("Failed to check"));
        
        println!("Nested mount points work correctly!");
    });
    
    executor.run_tasks_until_complete();
    println!("Nested mount points test passed!");
}

#[awkernel_lib::entry_point]
fn kernel_entry(_platform_info: awkernel_lib::platform::PlatformInfo) -> ! {
    println!("Starting VFS Registry tests...\n");
    
    test_vfs_registry_basic();
    println!();
    
    test_mount_aware_path_operations();
    println!();
    
    test_cross_filesystem_operations();
    println!();
    
    test_nested_mount_points();
    println!();
    
    println!("\nAll VFS Registry tests passed!");
    
    awkernel_lib::halt();
}