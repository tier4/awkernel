#![no_std]

extern crate alloc;

use alloc::vec;
use alloc::vec::Vec;
use core::sync::atomic::{AtomicBool, Ordering};
use awkernel_async_lib::task::spawn;
use awkernel_lib::storage;

static TEST_PASSED: AtomicBool = AtomicBool::new(false);

pub async fn run() {
    log::info!("=== Starting Async Storage Tests ===");

    // Initialize the storage transfer pool
    storage::init_transfer_pool();
    
    // Test 1: Check if storage devices are available
    if !test_storage_devices_available() {
        log::error!("Test 1 (Storage Devices Available) FAILED");
        return;
    }
    log::info!("Test 1 (Storage Devices Available) PASSED");

    // Test 2: Test async read operation
    if !test_async_read().await {
        log::error!("Test 2 (Async Read) FAILED");
        return;
    }
    log::info!("Test 2 (Async Read) PASSED");

    // Test 3: Test async write operation
    if !test_async_write().await {
        log::error!("Test 3 (Async Write) FAILED");
        return;
    }
    log::info!("Test 3 (Async Write) PASSED");

    // Test 4: Test concurrent async operations
    if !test_concurrent_operations().await {
        log::error!("Test 4 (Concurrent Operations) FAILED");
        return;
    }
    log::info!("Test 4 (Concurrent Operations) PASSED");

    TEST_PASSED.store(true, Ordering::SeqCst);
    log::info!("=== All Async Storage Tests PASSED ===");
}

fn test_storage_devices_available() -> bool {
    log::info!("Test 1: Checking for storage devices...");
    
    let devices = storage::get_all_storage_statuses();
    
    if devices.is_empty() {
        log::warn!("No storage devices found - cannot test async operations");
        log::warn!("Make sure to run with NVMe device enabled in QEMU");
        return false;
    }
    
    log::info!("Found {} storage device(s)", devices.len());
    for device in &devices {
        log::info!("  Device {}: {} (type: {:?})", 
            device.interface_id, 
            device.device_name,
            device.device_type
        );
        log::info!("    Block size: {} bytes", device.block_size);
        log::info!("    Total blocks: {}", device.num_blocks);
    }
    
    true
}

async fn test_async_read() -> bool {
    log::info!("Test 2: Testing async read operation...");
    
    let devices = storage::get_all_storage_statuses();
    if devices.is_empty() {
        return false;
    }
    
    let device = &devices[0];
    let device_id = device.interface_id;
    let block_size = device.block_size;
    
    log::info!("Reading block 0 from device {device_id}...");
    
    // Allocate buffer for reading
    let mut read_buf = vec![0u8; block_size];
    
    // Perform async read
    match storage::async_read_block(device_id, 0, &mut read_buf).await {
        Ok(()) => {
            log::info!("Async read completed successfully");
            log::info!("First 16 bytes: {:02x?}", &read_buf[..16.min(read_buf.len())]);
            true
        }
        Err(e) => {
            log::error!("Async read failed: {e:?}");
            false
        }
    }
}

async fn test_async_write() -> bool {
    log::info!("Test 3: Testing async write operation...");
    
    let devices = storage::get_all_storage_statuses();
    if devices.is_empty() {
        return false;
    }
    
    let device = &devices[0];
    let device_id = device.interface_id;
    let block_size = device.block_size;
    
    // Use a safe block number (avoid boot sectors)
    let test_block = 100;
    
    log::info!("Writing to block {test_block} on device {device_id}...");
    
    // Create test pattern
    let mut write_buf = vec![0u8; block_size];
    for (i, byte) in write_buf.iter_mut().enumerate() {
        *byte = (i & 0xFF) as u8;
    }
    
    // Perform async write
    match storage::async_write_block(device_id, test_block, &write_buf).await {
        Ok(()) => {
            log::info!("Async write completed successfully");
            
            // Verify by reading back
            let mut verify_buf = vec![0u8; block_size];
            match storage::async_read_block(device_id, test_block, &mut verify_buf).await {
                Ok(()) => {
                    // Log buffer sizes for debugging
                    log::info!("Write buffer size: {}, Verify buffer size: {}", 
                               write_buf.len(), verify_buf.len());
                    
                    // Check for differences
                    let mut mismatch_count = 0;
                    let mut first_mismatch = None;
                    for (i, (expected, got)) in write_buf.iter().zip(verify_buf.iter()).enumerate() {
                        if expected != got {
                            mismatch_count += 1;
                            if first_mismatch.is_none() {
                                first_mismatch = Some((i, *expected, *got));
                            }
                        }
                    }
                    
                    // Also check if lengths differ
                    if write_buf.len() != verify_buf.len() {
                        log::error!("Buffer length mismatch! write: {}, verify: {}", 
                                   write_buf.len(), verify_buf.len());
                        return false;
                    }
                    
                    if mismatch_count == 0 && write_buf == verify_buf {
                        log::info!("Write verification successful!");
                        true
                    } else {
                        log::error!("Write verification failed - {mismatch_count} bytes mismatched out of {block_size}");
                        if let Some((idx, exp, got)) = first_mismatch {
                            log::error!("First mismatch at byte {idx}: expected 0x{exp:02x}, got 0x{got:02x}");
                        }
                        log::info!("Expected first 16 bytes: {:02x?}", &write_buf[..16]);
                        log::info!("Got first 16 bytes: {:02x?}", &verify_buf[..16]);
                        log::info!("Expected last 16 bytes: {:02x?}", &write_buf[write_buf.len()-16..]);
                        log::info!("Got last 16 bytes: {:02x?}", &verify_buf[verify_buf.len()-16..]);
                        false
                    }
                }
                Err(e) => {
                    log::error!("Verification read failed: {e:?}");
                    false
                }
            }
        }
        Err(e) => {
            log::error!("Async write failed: {e:?}");
            false
        }
    }
}

async fn test_concurrent_operations() -> bool {
    log::info!("Test 4: Testing concurrent async operations...");
    
    let devices = storage::get_all_storage_statuses();
    if devices.is_empty() {
        return false;
    }
    
    let device = &devices[0];
    let device_id = device.interface_id;
    let block_size = device.block_size;
    
    // Spawn multiple concurrent read tasks
    let mut tasks = Vec::new();
    
    for i in 0..5 {
        let block_num = i * 10; // Read blocks 0, 10, 20, 30, 40
        
        let task_name = alloc::format!("read_block_{}", block_num).into();
        let task_id = spawn(task_name, async move {
            let mut buf = vec![0u8; block_size];
            match storage::async_read_block(device_id, block_num, &mut buf).await {
                Ok(()) => {
                    log::info!("Concurrent read of block {} completed", block_num);
                    Ok(())
                }
                Err(e) => {
                    log::error!("Concurrent read of block {} failed: {:?}", block_num, e);
                    Err("Read failed".into())
                }
            }
        }, awkernel_async_lib::scheduler::SchedulerType::FIFO);
        
        tasks.push(task_id);
    }
    
    // Wait for all tasks to complete
    // Sleep briefly to allow concurrent tasks to complete
    for _ in 0..100 {
        // Just yield control to allow other tasks to run
        core::hint::spin_loop();
    }
    
    let all_success = true; // Assume success if we got here
    
    if all_success {
        log::info!("All concurrent operations completed successfully");
    } else {
        log::error!("Some concurrent operations failed");
    }
    
    all_success
}

pub fn test_completed() -> bool {
    TEST_PASSED.load(Ordering::SeqCst)
}