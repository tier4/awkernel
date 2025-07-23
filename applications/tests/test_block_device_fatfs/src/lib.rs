#![no_std]

extern crate alloc;

use alloc::sync::Arc;
use alloc::vec;
use awkernel_lib::delay::wait_millisec;
use awkernel_lib::file::block_device::MemoryBlockDevice;
use awkernel_lib::file::fatfs::{create_fatfs_from_block_device, format_block_device_as_fat};
use awkernel_lib::file::io::{Read, Write, Seek};
use log::{info, error};

pub async fn run() {
    wait_millisec(1000);
    info!("Starting block device FAT filesystem integration test...\n");
    
    test_format_and_mount().await;
    test_file_operations().await;
    test_different_block_sizes().await;
    
    info!("\n=== Block Device FAT Filesystem Test Complete ===");
}

async fn test_format_and_mount() {
    info!("=== Testing Format and Mount ===");
    
    // Create a memory block device with 512-byte blocks, 2048 blocks (1MB)
    let device = Arc::new(MemoryBlockDevice::new(512, 2048));
    info!("Created 1MB block device with 512-byte blocks");
    
    // Format the device with FAT filesystem
    match format_block_device_as_fat(device.clone()) {
        Ok(()) => info!("✓ Successfully formatted block device as FAT"),
        Err(e) => {
            error!("✗ Failed to format block device: {}", e);
            return;
        }
    }
    
    // Create FAT filesystem from the formatted device
    match create_fatfs_from_block_device(device, false) {
        Ok(fs) => {
            info!("✓ Successfully created FAT filesystem from block device");
            
            // Try to get root directory
            let fs_arc = Arc::new(fs);
            let root = awkernel_lib::file::fatfs::fs::FileSystem::root_dir(&fs_arc);
            info!("✓ Successfully accessed root directory");
            
            // List entries (should be empty)
            let mut count = 0;
            for entry in root.iter() {
                match entry {
                    Ok(e) => {
                        info!("  Found entry: {}", e.file_name());
                        count += 1;
                    }
                    Err(e) => error!("  Error reading entry: {:?}", e),
                }
            }
            info!("  Total entries in root: {}", count);
        }
        Err(e) => error!("✗ Failed to create FAT filesystem: {}", e),
    }
}

async fn test_file_operations() {
    info!("\n=== Testing File Operations ===");
    
    // Create a larger block device with 4KB blocks
    let device = Arc::new(MemoryBlockDevice::new(4096, 512)); // 2MB total
    info!("Created 2MB block device with 4KB blocks");
    
    // Create and format FAT filesystem
    match create_fatfs_from_block_device(device, true) {
        Ok(fs) => {
            info!("✓ Created and formatted FAT filesystem");
            
            // Create a test file
            let fs_arc = Arc::new(fs);
            let root = awkernel_lib::file::fatfs::fs::FileSystem::root_dir(&fs_arc);
            {
                    match root.create_file("test.txt") {
                        Ok(mut file) => {
                            info!("✓ Created file: test.txt");
                            
                            // Write some data
                            let data = b"Hello from block device FAT filesystem!";
                            match Write::write_all(&mut file, data) {
                                Ok(()) => {
                                    info!("✓ Wrote {} bytes to file", data.len());
                                    
                                    // Flush to ensure data is written
                                    match file.flush() {
                                        Ok(()) => info!("✓ Flushed file data"),
                                        Err(e) => error!("✗ Failed to flush: {:?}", e),
                                    }
                                }
                                Err(e) => error!("✗ Failed to write data: {:?}", e),
                            }
                            
                            // Seek to beginning and read back
                            match file.seek(awkernel_lib::file::io::SeekFrom::Start(0)) {
                                Ok(_) => {
                                    let mut buf = vec![0u8; 100];
                                    match file.read(&mut buf) {
                                        Ok(n) => {
                                            info!("✓ Read {} bytes: {:?}", n, 
                                                  core::str::from_utf8(&buf[..n]).unwrap_or("<invalid>"));
                                        }
                                        Err(e) => error!("✗ Failed to read: {:?}", e),
                                    }
                                }
                                Err(e) => error!("✗ Failed to seek: {:?}", e),
                            }
                        }
                        Err(e) => error!("✗ Failed to create file: {:?}", e),
                    }
                    
                    // List directory again
                    info!("\nDirectory contents after file creation:");
                    for entry in root.iter() {
                        match entry {
                            Ok(e) => info!("  - {} ({} bytes)", 
                                          e.file_name(), 
                                          e.len()),
                            Err(e) => error!("  Error: {:?}", e),
                        }
                    }
            }
        }
        Err(e) => error!("✗ Failed to create FAT filesystem: {}", e),
    }
}

async fn test_different_block_sizes() {
    info!("\n=== Testing Different Block Sizes ===");
    
    let block_sizes = [(512, 4096), (1024, 2048), (2048, 1024), (4096, 512)];
    
    for (block_size, num_blocks) in &block_sizes {
        let total_size = block_size * num_blocks;
        info!("\nTesting {} byte blocks x {} blocks = {} KB", 
              block_size, num_blocks, total_size / 1024);
        
        let device = Arc::new(MemoryBlockDevice::new(*block_size, *num_blocks as u64));
        
        match create_fatfs_from_block_device(device, true) {
            Ok(fs) => {
                info!("  ✓ Successfully created FAT filesystem");
                
                // Get filesystem stats
                let fs_arc = Arc::new(fs);
                let stats_result = awkernel_lib::file::fatfs::fs::FileSystem::stats(&fs_arc);
                match stats_result {
                    Ok(stats) => {
                        info!("  Cluster size: {} bytes", stats.cluster_size());
                        info!("  Total clusters: {}", stats.total_clusters());
                        info!("  Free clusters: {}", stats.free_clusters());
                    }
                    Err(e) => error!("  Failed to get stats: {:?}", e),
                }
            }
            Err(e) => error!("  ✗ Failed to create FAT filesystem: {}", e),
        }
    }
}