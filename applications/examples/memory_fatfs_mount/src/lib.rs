#![no_std]
#![no_main]

extern crate alloc;

use alloc::string::ToString;
use awkernel_async_lib::{
    executor::Executor,
    file::{
        mount::{mount, MountOptions},
        filesystem::AsyncSeekAndWrite,
        mount_aware_vfs_path::MountAwareAsyncVfsPath,
    },
};
use alloc::collections::BTreeMap;
use awkernel_lib::{print, println, file::memfs::{create_memory_block_device, DEFAULT_BLOCK_SIZE}};

#[awkernel_lib::entry_point]
fn kernel_entry(_platform_info: awkernel_lib::platform::PlatformInfo) -> ! {
    println!("Memory FatFS Mount Example");
    println!("==========================\n");
    
    // Create an async executor
    let executor = Executor::spawn_executor(None, 512);
    
    executor.spawn_detached(async {
        // Create a memory block device
        println!("\nCreating memory block device...");
        let device = create_memory_block_device(4 * 1024 * 1024, DEFAULT_BLOCK_SIZE)
            .expect("Failed to create memory block device");
        println!("✓ Memory block device created (4MB)");
        
        // Mount with format option
        let mut options = MountOptions::new();
        options.fs_options.insert("format".into(), "true".into());
        
        println!("\nMounting memory FatFS at /data...");
        mount(
            "/data",
            "memfs",
            "fatfs",
            device,
            options,
        ).await.expect("Failed to mount filesystem");
        println!("✓ Memory filesystem mounted at /data");
        
        // Create a directory structure
        println!("\nCreating directory structure...");
        let docs_dir = MountAwareAsyncVfsPath::new("/data/documents");
        docs_dir.create_dir().await.expect("Failed to create documents dir");
        
        let images_dir = MountAwareAsyncVfsPath::new("/data/images");
        images_dir.create_dir().await.expect("Failed to create images dir");
        println!("✓ Created /data/documents and /data/images");
        
        // Write some files
        println!("\nWriting files...");
        
        // Write a text file
        let readme_path = MountAwareAsyncVfsPath::new("/data/documents/readme.txt");
        let mut readme = readme_path.create_file().await.expect("Failed to create readme");
        readme.write_all(b"Welcome to AWKernel Memory FatFS!\n").await.expect("Failed to write");
        readme.write_all(b"This filesystem is stored entirely in memory.\n").await.expect("Failed to write");
        readme.flush().await.expect("Failed to flush");
        drop(readme);
        println!("✓ Created /data/documents/readme.txt");
        
        // Write a config file
        let config_path = MountAwareAsyncVfsPath::new("/data/config.ini");
        let mut config = config_path.create_file().await.expect("Failed to create config");
        config.write_all(b"[system]\n").await.expect("Failed to write");
        config.write_all(b"version=1.0\n").await.expect("Failed to write");
        config.write_all(b"debug=true\n").await.expect("Failed to write");
        config.flush().await.expect("Failed to flush");
        drop(config);
        println!("✓ Created /data/config.ini");
        
        // List directory contents
        println!("\nListing /data contents:");
        let data_dir = MountAwareAsyncVfsPath::new("/data");
        let entries = data_dir.read_dir().await.expect("Failed to read directory");
        
        for entry in entries {
            let metadata = entry.metadata().await.expect("Failed to get metadata");
            let type_str = if metadata.file_type == awkernel_lib::file::vfs::path::VfsFileType::Directory {
                "[DIR] "
            } else {
                "[FILE]"
            };
            
            if let Some(filename) = entry.filename() {
                println!("  {} {}", type_str, filename);
            }
        }
        
        // Read back the readme file
        println!("\nReading back readme.txt:");
        let mut reader = readme_path.open_file().await.expect("Failed to open readme");
        let mut contents = alloc::string::String::new();
        reader.read_to_string(&mut contents).await.expect("Failed to read");
        print!("{}", contents);
        
        // Demonstrate metadata
        println!("\nFile metadata:");
        let meta = readme_path.metadata().await.expect("Failed to get metadata");
        println!("  Size: {} bytes", meta.len);
        println!("  Type: {:?}", meta.file_type);
        
        // Mount another filesystem
        println!("\nMounting second filesystem at /backup...");
        
        // Create a memory block device for backup
        let backup_device = create_memory_block_device(1024 * 1024, 512)
            .expect("Failed to create backup memory block device");
        
        // Mount with format option
        let mut backup_options = MountOptions::new();
        backup_options.fs_options.insert("format".into(), "true".into());
        
        mount(
            "/backup",
            "backup",
            "fatfs",
            backup_device,
            backup_options,
        ).await.expect("Failed to mount backup filesystem");
        println!("✓ Backup filesystem mounted");
        
        // Copy file between filesystems
        println!("\nCopying readme.txt to /backup...");
        let backup_readme = MountAwareAsyncVfsPath::new("/backup/readme.txt");
        readme_path.copy_file(&backup_readme).await.expect("Failed to copy file");
        println!("✓ File copied successfully");
        
        // Verify the copy
        let backup_meta = backup_readme.metadata().await.expect("Failed to get backup metadata");
        println!("  Backup file size: {} bytes", backup_meta.len);
        
        println!("\n✅ Example completed successfully!");
    });
    
    // Run the async tasks
    executor.run_tasks_until_complete();
    
    println!("\nMemory FatFS demonstration complete.");
    awkernel_lib::halt();
}