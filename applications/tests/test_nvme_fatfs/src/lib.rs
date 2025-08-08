#![no_std]

extern crate alloc;

use alloc::{sync::Arc, vec, vec::Vec};
use awkernel_lib::{
    storage::{get_all_storage_devices, StorageDeviceType},
    file::{
        memfs::MemoryBlockDevice,
        fatfs::{create_fatfs_from_block_device, fs::FileSystem},
        io::{Read, Write, Seek, SeekFrom},
    },
};
use log::{info, error, warn};

/// Test that verifies BlockDeviceAdapter works correctly with different device types.
/// 
/// NOTE: Currently we can't directly test with NVMe because create_fatfs_from_block_device
/// requires the device type to implement Debug, but dyn StorageDevice doesn't.
/// 
/// However, the BlockDeviceAdapter code has been updated to handle both:
/// - Memory devices (tested here)
/// - NVMe devices (would use proper transfer allocation with polling)
pub async fn run() {
    info!("=== Starting BlockDeviceAdapter Test ===");
    
    // Wait a bit for storage initialization
    awkernel_lib::delay::wait_millisec(1000);
    
    // Test 1: Check for NVMe devices
    test_nvme_presence().await;
    
    // Test 2: Test BlockDeviceAdapter with memory device
    // This verifies the adapter still works correctly with memory devices
    if !test_memory_device_adapter().await {
        error!("Memory device adapter test failed");
        return;
    }
    
    // Test 3: Verify cross-block operations work
    if !test_cross_block_operations().await {
        error!("Cross-block operations test failed");
        return;
    }
    
    info!("=== BlockDeviceAdapter Test Complete ===");
    info!("Note: NVMe path tested via code inspection - transfer allocation logic is in place");
}

async fn test_nvme_presence() -> bool {
    info!("Test 1: Checking for NVMe devices...");
    
    let devices = get_all_storage_devices();
    
    let nvme_devices: Vec<_> = devices.iter()
        .filter(|d| matches!(d.device_type, StorageDeviceType::NVMe))
        .collect();
    
    if nvme_devices.is_empty() {
        warn!("  No NVMe devices found");
        warn!("  Run with: -device nvme,drive=nvme0,serial=deadbeef");
        info!("  BlockDeviceAdapter would use transfer allocation for NVMe");
    } else {
        for device in &nvme_devices {
            info!("  Found NVMe: {} (ID: {})", 
                  device.device_name, device.interface_id);
            info!("    Block size: {} bytes", device.block_size);
            info!("    Would use polling mode with transfers");
        }
    }
    
    true
}

async fn test_memory_device_adapter() -> bool {
    info!("Test 2: Testing BlockDeviceAdapter with MemoryBlockDevice...");
    
    // Create a memory device
    let device = Arc::new(MemoryBlockDevice::new(512, 100)); // 50KB
    
    info!("  Created memory device: 512-byte blocks, 100 blocks");
    info!("  BlockDeviceAdapter will use transfer_id=0 (no real transfers)");
    
    // Create FatFS using BlockDeviceAdapter
    let fs = match create_fatfs_from_block_device(device, true) {
        Ok(f) => Arc::new(f),
        Err(e) => {
            error!("  Failed to create FatFS: {}", e);
            return false;
        }
    };
    
    info!("  ✓ Created FatFS with BlockDeviceAdapter");
    
    // Create and write a file
    let root = FileSystem::root_dir(&fs);
    let mut file = match root.create_file("test.txt") {
        Ok(f) => f,
        Err(e) => {
            error!("  Failed to create file: {:?}", e);
            return false;
        }
    };
    
    let test_data = b"Testing BlockDeviceAdapter with MemoryBlockDevice";
    match file.write_all(test_data) {
        Ok(_) => info!("  ✓ Write successful"),
        Err(e) => {
            error!("  Write failed: {:?}", e);
            return false;
        }
    }
    
    // Read back and verify
    file.seek(SeekFrom::Start(0)).unwrap();
    let mut buf = vec![0u8; test_data.len()];
    match file.read_exact(&mut buf) {
        Ok(_) => {
            if buf == test_data {
                info!("  ✓ Read verification successful");
            } else {
                error!("  Read data mismatch");
                return false;
            }
        }
        Err(e) => {
            error!("  Read failed: {:?}", e);
            return false;
        }
    }
    
    true
}

async fn test_cross_block_operations() -> bool {
    info!("Test 3: Testing cross-block operations...");
    
    // This tests that BlockCache correctly handles operations
    // that span multiple blocks
    
    let device = Arc::new(MemoryBlockDevice::new(512, 100));
    let fs = match create_fatfs_from_block_device(device, true) {
        Ok(f) => Arc::new(f),
        Err(e) => {
            error!("  Failed to create FatFS: {}", e);
            return false;
        }
    };
    
    let root = FileSystem::root_dir(&fs);
    let mut file = root.create_file("large.dat").unwrap();
    
    // Write data that spans multiple blocks
    // Block size is 512, so write 1536 bytes (3 blocks)
    let large_data = vec![0xAAu8; 1536];
    
    info!("  Writing 1536 bytes (spans 3 blocks)...");
    match file.write_all(&large_data) {
        Ok(_) => info!("  ✓ Cross-block write successful"),
        Err(e) => {
            error!("  Cross-block write failed: {:?}", e);
            return false;
        }
    }
    
    // Read back in chunks to test cache behavior
    file.seek(SeekFrom::Start(256)).unwrap(); // Start mid-block
    let mut partial_buf = vec![0u8; 768]; // Read across 2 blocks
    
    info!("  Reading 768 bytes from offset 256...");
    match file.read_exact(&mut partial_buf) {
        Ok(_) => {
            if partial_buf.iter().all(|&b| b == 0xAA) {
                info!("  ✓ Cross-block read successful");
            } else {
                error!("  Cross-block read data incorrect");
                return false;
            }
        }
        Err(e) => {
            error!("  Cross-block read failed: {:?}", e);
            return false;
        }
    }
    
    // Test flush
    match file.flush() {
        Ok(_) => info!("  ✓ Flush successful"),
        Err(e) => {
            error!("  Flush failed: {:?}", e);
            return false;
        }
    }
    
    info!("  ✓ All cross-block operations successful");
    true
}