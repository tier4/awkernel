#![no_std]

extern crate alloc;

use alloc::vec::Vec;
use awkernel_lib::{
    delay::{uptime, wait_millisec},
    storage::{
        allocate_transfer, free_transfer, get_all_storage_statuses, get_storage_device,
        transfer_get_status, transfer_is_completed, transfer_set_params, transfer_set_poll_mode,
        StorageDevice, StorageDeviceType,
    },
};
use core::sync::atomic::{AtomicBool, Ordering};

static TEST_PASSED: AtomicBool = AtomicBool::new(false);

/// Helper function to wait for transfer completion
fn wait_for_transfer_completion(transfer_id: u16, timeout_ms: u32) -> bool {
    let start = uptime() / 1000; // Convert us to ms
    
    loop {
        if let Ok(completed) = transfer_is_completed(transfer_id) {
            if completed {
                // Check final status
                if let Ok(status) = transfer_get_status(transfer_id) {
                    if status != 0 {
                        log::error!("Transfer failed with status code: 0x{:x}", status);
                        return false;
                    }
                    return true;
                }
            }
        }
        
        let elapsed = (uptime() / 1000) - start;
        if elapsed > timeout_ms as u64 {
            log::error!("Transfer timeout after {}ms", timeout_ms);
            return false;
        }
        
        core::hint::spin_loop();
    }
}

pub async fn run() {
    log::info!("=== Starting NVMe Driver Tests ===");

    // Wait for storage initialization
    wait_millisec(1000);

    // Test A: Device Detection and Namespace Registration
    if !test_device_detection() {
        log::error!("Test A (Device Detection) FAILED");
        return;
    }
    log::info!("Test A (Device Detection) PASSED");

    // Test B: Multi-block Operations with different sizes
    if !test_multi_block_operations().await {
        log::error!("Test B (Multi-block Operations) FAILED");
        return;
    }
    log::info!("Test B (Multi-block Operations) PASSED");

    // Test C: Polling Mode Tests
    if !test_io_mode(true).await {
        log::error!("Test C (I/O - Polling) FAILED");
        return;
    }
    log::info!("Test C (I/O - Polling) PASSED");

    // Test D: Interrupt Mode Tests
    if !test_io_mode(false).await {
        log::error!("Test D (I/O - Interrupt) FAILED");
        return;
    }
    log::info!("Test D (I/O - Interrupt) PASSED");

    // Test E: Flush Operations
    if !test_flush_operations().await {
        log::error!("Test E (Flush Operations) FAILED");
        return;
    }
    log::info!("Test E (Flush Operations) PASSED");

    TEST_PASSED.store(true, Ordering::SeqCst);
    log::info!("=== All NVMe Tests PASSED ===");
}

fn test_device_detection() -> bool {
    log::info!("Test A: Checking NVMe device detection and namespace registration...");

    // Check namespace registration in storage manager
    let devices = get_all_storage_statuses();
    let nvme_devices: Vec<_> = devices
        .iter()
        .filter(|d| matches!(d.device_type, StorageDeviceType::NVMe))
        .collect();

    if nvme_devices.is_empty() {
        log::warn!("No NVMe devices detected - this is OK if no NVMe device is present");
        log::warn!("Run with: -device nvme,drive=nvme0,serial=deadbeef");
        return true; // Don't fail if no device
    }

    for device in &nvme_devices {
        log::info!(
            "  Namespace registered: {} (ID: {})",
            device.device_name, device.interface_id
        );
        log::info!(
            "    Block size: {} bytes, Total blocks: {}",
            device.block_size, device.num_blocks
        );

        // Verify reasonable properties
        if device.block_size != 512 && device.block_size != 4096 {
            log::error!("Unexpected block size: {} bytes", device.block_size);
            return false;
        }

        if device.num_blocks == 0 {
            log::error!("Namespace reports 0 blocks");
            return false;
        }

        if device.irqs.is_empty() {
            log::error!("NVMe namespace has no IRQs configured");
            return false;
        }
    }

    log::info!("  ✓ NVMe namespaces properly registered with storage manager");
    true
}

async fn test_multi_block_operations() -> bool {
    log::info!("Test B: Testing multi-block read/write operations...");

    // Get the first NVMe device
    let devices = get_all_storage_statuses();
    let nvme_device = devices
        .iter()
        .find(|d| matches!(d.device_type, StorageDeviceType::NVMe));

    let device_status = match nvme_device {
        Some(d) => d,
        None => {
            log::warn!("No NVMe device available for multi-block test");
            return true;
        }
    };

    let device_id = device_status.interface_id;
    let block_size = device_status.block_size;

    // Get the actual device
    let device = match get_storage_device(device_id) {
        Ok(d) => d,
        Err(e) => {
            log::error!("Failed to get storage device: {:?}", e);
            return false;
        }
    };

    // Test different block counts
    // These test different PRP scenarios:
    // - 8 blocks (4KB with 512B blocks) - tests 1 page
    // - 16 blocks (8KB) - tests 2 pages (uses PRP1 and PRP2)
    // - 32 blocks (16KB) - tests 4 pages (uses PRP list)
    // - 64 blocks (32KB) - tests 8 pages (larger PRP list)
    // - 128 blocks (64KB) - tests 16 pages (stress test PRP list)
    
    let test_configs = [
        (8, "8 blocks (4KB)"),
        (16, "16 blocks (8KB)"),
        (32, "32 blocks (16KB)"),
        (64, "64 blocks (32KB)"),
        (128, "128 blocks (64KB)"),
    ];

    for (num_blocks, description) in &test_configs {
        log::info!("  Testing {description}...");
        
        if !test_blocks_rw(device.clone(), device_id, *num_blocks, block_size).await {
            log::error!("    Failed {description} test");
            return false;
        }
        
        log::info!("    ✓ {description} test passed");
    }

    true
}

async fn test_blocks_rw(
    device: alloc::sync::Arc<dyn awkernel_lib::storage::StorageDevice>,
    device_id: u64,
    num_blocks: u32,
    block_size: usize,
) -> bool {
    let buffer_size = num_blocks as usize * block_size;
    let test_lba = 100; // Start LBA for testing

    // Create write buffer with test pattern
    let mut write_buf = alloc::vec![0u8; buffer_size];
    for (i, byte) in write_buf.iter_mut().enumerate() {
        // Create pattern that changes across page boundaries
        let page_num = i / 4096;
        let offset_in_page = i % 4096;
        *byte = ((page_num as u8) ^ (offset_in_page as u8)) ^ 0xAA;
    }

    // Allocate transfer for write
    let write_transfer = match allocate_transfer(device_id) {
        Ok(id) => id,
        Err(e) => {
            log::error!("Failed to allocate write transfer: {:?}", e);
            return false;
        }
    };

    // Set transfer parameters
    if let Err(e) = transfer_set_params(write_transfer, test_lba, num_blocks, false, 1) {
        log::error!("Failed to set write transfer params: {:?}", e);
        free_transfer(write_transfer);
        return false;
    }

    // Use polling mode for predictable testing
    transfer_set_poll_mode(write_transfer, true, 5000);

    // Perform write
    if let Err(e) = device.write_blocks(&write_buf, write_transfer) {
        log::error!("Write failed: {:?}", e);
        free_transfer(write_transfer);
        return false;
    }

    // Wait for write completion
    if !wait_for_transfer_completion(write_transfer, 5000) {
        log::error!("Write transfer did not complete");
        free_transfer(write_transfer);
        return false;
    }

    free_transfer(write_transfer);

    // Allocate transfer for read
    let read_transfer = match allocate_transfer(device_id) {
        Ok(id) => id,
        Err(e) => {
            log::error!("Failed to allocate read transfer: {:?}", e);
            return false;
        }
    };

    // Set transfer parameters for read
    if let Err(e) = transfer_set_params(read_transfer, test_lba, num_blocks, true, 1) {
        log::error!("Failed to set read transfer params: {:?}", e);
        free_transfer(read_transfer);
        return false;
    }

    transfer_set_poll_mode(read_transfer, true, 5000);

    // Create read buffer
    let mut read_buf = alloc::vec![0u8; buffer_size];

    // Perform read
    if let Err(e) = device.read_blocks(&mut read_buf, read_transfer) {
        log::error!("Read failed: {:?}", e);
        free_transfer(read_transfer);
        return false;
    }

    // Wait for read completion
    if !wait_for_transfer_completion(read_transfer, 5000) {
        log::error!("Read transfer did not complete");
        free_transfer(read_transfer);
        return false;
    }

    free_transfer(read_transfer);

    // Verify data
    let mut mismatches = 0;
    for (i, (expected, actual)) in write_buf.iter().zip(read_buf.iter()).enumerate() {
        if expected != actual {
            if mismatches < 10 {
                log::error!(
                    "Data mismatch at offset {}: expected 0x{:02x}, got 0x{:02x}",
                    i, expected, actual
                );
            }
            mismatches += 1;
        }
    }

    if mismatches > 0 {
        log::error!(
            "Data verification failed: {} mismatches out of {} bytes",
            mismatches, buffer_size
        );
        false
    } else {
        true
    }
}

async fn test_io_mode(polling: bool) -> bool {
    let mode_str = if polling { "Polling" } else { "Interrupt" };
    log::info!("Test: Testing I/O in {} mode...", mode_str);

    let devices = get_all_storage_statuses();
    let nvme_device = devices
        .iter()
        .find(|d| matches!(d.device_type, StorageDeviceType::NVMe));

    let device_status = match nvme_device {
        Some(d) => d,
        None => {
            log::warn!("No NVMe device available");
            return true;
        }
    };

    let device_id = device_status.interface_id;
    let device = match get_storage_device(device_id) {
        Ok(d) => d,
        Err(e) => {
            log::error!("Failed to get storage device: {:?}", e);
            return false;
        }
    };

    // Test with 8 blocks
    let num_blocks = 8;
    let block_size = device_status.block_size;
    let buffer_size = num_blocks * block_size;
    let test_lba = 200;

    // Create test buffer
    let mut buffer = alloc::vec![0x55u8; buffer_size];

    // Write test
    let transfer = match allocate_transfer(device_id) {
        Ok(id) => id,
        Err(e) => {
            log::error!("Failed to allocate transfer: {:?}", e);
            return false;
        }
    };

    transfer_set_params(transfer, test_lba, num_blocks as u32, false, 1).unwrap();
    transfer_set_poll_mode(transfer, polling, 5000);

    if let Err(e) = device.write_blocks(&buffer, transfer) {
        log::error!("Write failed in {} mode: {:?}", mode_str, e);
        free_transfer(transfer);
        return false;
    }

    if !wait_for_transfer_completion(transfer, 5000) {
        log::error!("Transfer timeout in {} mode", mode_str);
        free_transfer(transfer);
        return false;
    }

    free_transfer(transfer);

    // Read test
    let transfer = match allocate_transfer(device_id) {
        Ok(id) => id,
        Err(e) => {
            log::error!("Failed to allocate transfer: {:?}", e);
            return false;
        }
    };

    transfer_set_params(transfer, test_lba, num_blocks as u32, true, 1).unwrap();
    transfer_set_poll_mode(transfer, polling, 5000);

    buffer.fill(0);
    if let Err(e) = device.read_blocks(&mut buffer, transfer) {
        log::error!("Read failed in {} mode: {:?}", mode_str, e);
        free_transfer(transfer);
        return false;
    }

    if !wait_for_transfer_completion(transfer, 5000) {
        log::error!("Transfer timeout in {} mode", mode_str);
        free_transfer(transfer);
        return false;
    }

    free_transfer(transfer);

    // Verify data
    for (i, &byte) in buffer.iter().enumerate() {
        if byte != 0x55 {
            log::error!("Data mismatch at offset {}: expected 0x55, got 0x{:02x}", i, byte);
            return false;
        }
    }

    log::info!("  ✓ {} mode I/O test passed", mode_str);
    true
}

async fn test_flush_operations() -> bool {
    log::info!("Test E: Testing flush operations...");

    let devices = get_all_storage_statuses();
    let nvme_device = devices
        .iter()
        .find(|d| matches!(d.device_type, StorageDeviceType::NVMe));

    let device_status = match nvme_device {
        Some(d) => d,
        None => {
            log::warn!("No NVMe device available");
            return true;
        }
    };

    let device_id = device_status.interface_id;
    let device = match get_storage_device(device_id) {
        Ok(d) => d,
        Err(e) => {
            log::error!("Failed to get storage device: {:?}", e);
            return false;
        }
    };

    // Test flush in both polling and interrupt modes
    for polling in [true, false] {
        let mode_str = if polling { "polling" } else { "interrupt" };
        
        let transfer = match allocate_transfer(device_id) {
            Ok(id) => id,
            Err(e) => {
                log::error!("Failed to allocate transfer for flush: {:?}", e);
                return false;
            }
        };

        transfer_set_poll_mode(transfer, polling, 5000);

        if let Err(e) = device.flush(transfer) {
            log::error!("Flush failed in {} mode: {:?}", mode_str, e);
            free_transfer(transfer);
            return false;
        }

        if !wait_for_transfer_completion(transfer, 5000) {
            log::error!("Flush timeout in {} mode", mode_str);
            free_transfer(transfer);
            return false;
        }

        free_transfer(transfer);
        log::info!("  ✓ Flush in {} mode passed", mode_str);
    }

    true
}

pub fn is_test_complete() -> bool {
    TEST_PASSED.load(Ordering::SeqCst)
}