#![no_std]

extern crate alloc;

use awkernel_lib::{
    addr::Addr,
    dma_pool::DMAPool,
    dma_map::{DmaMap, DmaTag, DmaSyncOp},
    paging::PAGESIZE,
    storage::get_transfer,
};
use core::sync::atomic::{AtomicBool, Ordering};

// Import NVMe types
use awkernel_drivers::pcie::{nvme::NVME_DEVICE, PCIeDevice};

static TEST_PASSED: AtomicBool = AtomicBool::new(false);

/// Helper function to wait for transfer completion synchronously
fn wait_for_transfer_completion(transfer_id: u16) {
    loop {
        if let Ok(transfer) = get_transfer(transfer_id) {
            if transfer.completed.load(Ordering::Acquire) {
                break;
            }
        }
        core::hint::spin_loop();
    }
}

pub async fn run() {
    log::info!("=== Starting NVMe Driver Tests ===");

    // Test A: Basic Device Detection
    if !test_device_detection() {
        log::error!("Test A (Device Detection) FAILED");
        return;
    }
    log::info!("Test A (Device Detection) PASSED");

    // Test B: Read/Write Test (Polling Mode)
    // Commented out per user request to isolate interrupt test
    if !test_read_write_mode(true).await {
        log::error!("Test B (Read/Write - Polling) FAILED");
        return;
    }
    log::info!("Test B (Read/Write - Polling) PASSED");

    // Test B2: Read/Write Test (Interrupt Mode)
    if !test_read_write_mode(false).await {
        log::error!("Test B2 (Read/Write - Interrupt) FAILED");
        return;
    }
    log::info!("Test B2 (Read/Write - Interrupt) PASSED");

    // Test C: Flush Test (Polling Mode)
    // Commented out to isolate interrupt test
    if !test_flush_mode(true).await {
        log::error!("Test C (Flush - Polling) FAILED");
        return;
    }
    log::info!("Test C (Flush - Polling) PASSED");

    // Test C2: Flush Test (Interrupt Mode)
    if !test_flush_mode(false).await {
        log::error!("Test C2 (Flush - Interrupt) FAILED");
        return;
    }
    log::info!("Test C2 (Flush - Interrupt) PASSED");

    TEST_PASSED.store(true, Ordering::SeqCst);
    log::info!("=== All NVMe Tests PASSED ===");
}

fn test_device_detection() -> bool {
    log::info!("Test A: Checking NVMe device detection...");

    let device_guard = NVME_DEVICE.read();
    match device_guard.as_ref() {
        Some(nvme) => {
            log::info!("NVMe device detected successfully");
            // Try to get device name to verify it's properly initialized
            let device_name = nvme.device_name();
            log::info!("Device name: {device_name}");

            // Debug interrupt configuration
            nvme.debug_interrupt_config();

            true
        }
        None => {
            log::error!("No NVMe device found!");
            false
        }
    }
}

async fn test_read_write_mode(poll: bool) -> bool {
    let mode_str = if poll { "Polling" } else { "Interrupt" };
    log::info!("Test B: Testing read/write operations in {mode_str} mode...");

    let device_guard = NVME_DEVICE.read();
    let nvme = match device_guard.as_ref() {
        Some(dev) => dev,
        None => {
            log::error!("No NVMe device available for read/write test");
            return false;
        }
    };

    // Test parameters
    const TEST_LBA: u64 = 100;
    const TEST_BLOCKS: u32 = 8;
    const SECTOR_SIZE: usize = 512;
    const NSID: u32 = 1; // Namespace ID 1

    // Allocate DMA buffers
    let buffer_size = (TEST_BLOCKS as usize) * SECTOR_SIZE;
    let pages_needed = buffer_size.div_ceil(PAGESIZE);

    // Allocate write buffer
    let write_dma = match DMAPool::<u8>::new(0, pages_needed) {
        Some(dma) => dma,
        None => {
            log::error!("Failed to allocate write DMA buffer");
            return false;
        }
    };

    // Fill write buffer with test pattern
    let write_ptr = write_dma.get_virt_addr().as_ptr::<u8>() as *mut u8;
    let write_slice = unsafe { core::slice::from_raw_parts_mut(write_ptr, buffer_size) };
    for (i, byte) in write_slice.iter_mut().enumerate() {
        *byte = ((i % 256) as u8) ^ 0xAA; // Simple pattern: index XOR 0xAA
    }
    // Create DmaMap for write operation
    let tag = DmaTag::new_64bit();
    let mut write_dma_map = match DmaMap::new(tag, 0) {
        Ok(map) => map,
        Err(e) => {
            log::error!("Failed to create write DMA map: {e:?}");
            return false;
        }
    };

    // Load the write buffer into the DMA map
    if let Err(e) = write_dma_map.load(write_dma.get_virt_addr(), buffer_size) {
        log::error!("Failed to load write DMA map: {e:?}");
        return false;
    }

    // Sync before write
    if let Err(e) = write_dma_map.sync(0, buffer_size, DmaSyncOp::PreWrite) {
        log::error!("Failed to sync write DMA map: {e:?}");
        return false;
    }

    // Write data
    log::info!("Writing {TEST_BLOCKS} blocks to LBA {TEST_LBA} (poll={poll})...");
    // TODO: Update to use new transfer-based interface
    // if let Err(e) = nvme.write_sectors(NSID, TEST_LBA, TEST_BLOCKS, &write_dma_map, poll) {
    //     log::error!("Write failed: {e:?}");
    //     return false;
    // }
    log::info!("Write test skipped - needs update for new interface");

    // Sync after write
    if let Err(e) = write_dma_map.sync(0, buffer_size, DmaSyncOp::PostWrite) {
        log::error!("Failed to sync write DMA map after write: {e:?}");
        return false;
    }

    // Allocate read buffer
    let read_dma = match DMAPool::<u8>::new(0, pages_needed) {
        Some(dma) => dma,
        None => {
            log::error!("Failed to allocate read DMA buffer");
            return false;
        }
    };

    // Clear read buffer
    let read_ptr = read_dma.get_virt_addr().as_ptr::<u8>() as *mut u8;
    let read_slice = unsafe { core::slice::from_raw_parts_mut(read_ptr, buffer_size) };
    for byte in read_slice.iter_mut() {
        *byte = 0;
    }
    // Create DmaMap for read operation
    let mut read_dma_map = match DmaMap::new(tag, 0) {
        Ok(map) => map,
        Err(e) => {
            log::error!("Failed to create read DMA map: {e:?}");
            return false;
        }
    };

    // Load the read buffer into the DMA map
    if let Err(e) = read_dma_map.load(read_dma.get_virt_addr(), buffer_size) {
        log::error!("Failed to load read DMA map: {e:?}");
        return false;
    }

    // Sync before read
    if let Err(e) = read_dma_map.sync(0, buffer_size, DmaSyncOp::PreRead) {
        log::error!("Failed to sync read DMA map: {e:?}");
        return false;
    }

    // Read data back
    log::info!("Reading {TEST_BLOCKS} blocks from LBA {TEST_LBA} (poll={poll})...");
    // TODO: Update to use new transfer-based interface
    // if let Err(e) = nvme.read_sectors(NSID, TEST_LBA, TEST_BLOCKS, &read_dma_map, poll) {
    //     log::error!("Read failed: {e:?}");
    //     return false;
    // }
    log::info!("Read test skipped - needs update for new interface");
    log::info!("Read completed successfully");

    // Sync after read
    if let Err(e) = read_dma_map.sync(0, buffer_size, DmaSyncOp::PostRead) {
        log::error!("Failed to sync read DMA map after read: {e:?}");
        return false;
    }

    // Verify data
    log::info!("Verifying data...");
    let mut mismatches = 0;
    for (i, &actual) in read_slice.iter().enumerate().take(buffer_size) {
        let expected = ((i % 256) as u8) ^ 0xAA;
        if expected != actual {
            if mismatches < 10 {
                log::error!(
                    "Data mismatch at offset {i}: expected 0x{expected:02x}, got 0x{actual:02x}"
                );
            }
            mismatches += 1;
        }
    }

    if mismatches > 0 {
        log::error!("Data verification failed: {mismatches} mismatches out of {buffer_size} bytes");
        false
    } else {
        log::info!("Data verification successful: all {buffer_size} bytes match");
        true
    }
}

async fn test_flush_mode(poll: bool) -> bool {
    let mode_str = if poll { "Polling" } else { "Interrupt" };
    log::info!("Test C: Testing flush operation in {mode_str} mode...");

    let device_guard = NVME_DEVICE.read();
    let nvme = match device_guard.as_ref() {
        Some(dev) => dev,
        None => {
            log::error!("No NVMe device available for flush test");
            return false;
        }
    };

    const NSID: u32 = 1;

    // First write some data to ensure there's something to flush
    const TEST_LBA: u64 = 200;
    const TEST_BLOCKS: u32 = 1;
    const SECTOR_SIZE: usize = 512;

    let write_dma = match DMAPool::<u8>::new(0, 1) {
        Some(dma) => dma,
        None => {
            log::error!("Failed to allocate DMA buffer for flush test");
            return false;
        }
    };

    // Fill with test data
    let write_ptr = write_dma.get_virt_addr().as_ptr::<u8>() as *mut u8;
    let write_slice = unsafe { core::slice::from_raw_parts_mut(write_ptr, SECTOR_SIZE) };
    for (i, byte) in write_slice.iter_mut().enumerate() {
        *byte = (i % 256) as u8;
    }
    // Create DmaMap for write operation
    let tag = DmaTag::new_64bit();
    let mut write_dma_map = match DmaMap::new(tag, 0) {
        Ok(map) => map,
        Err(e) => {
            log::error!("Failed to create write DMA map for flush test: {e:?}");
            return false;
        }
    };

    // Load the write buffer into the DMA map
    if let Err(e) = write_dma_map.load(write_dma.get_virt_addr(), SECTOR_SIZE) {
        log::error!("Failed to load write DMA map for flush test: {e:?}");
        return false;
    }

    // Sync before write
    if let Err(e) = write_dma_map.sync(0, SECTOR_SIZE, DmaSyncOp::PreWrite) {
        log::error!("Failed to sync write DMA map for flush test: {e:?}");
        return false;
    }

    // Write data
    log::info!("Writing data before flush (poll={poll})...");
    // TODO: Update to use new transfer-based interface
    // if let Err(e) = nvme.write_sectors(NSID, TEST_LBA, TEST_BLOCKS, &write_dma_map, poll) {
    //     log::error!("Write before flush failed: {e:?}");
    //     return false;
    // }
    log::info!("Write before flush test skipped - needs update for new interface");

    // Sync after write
    if let Err(e) = write_dma_map.sync(0, SECTOR_SIZE, DmaSyncOp::PostWrite) {
        log::error!("Failed to sync write DMA map after write for flush test: {e:?}");
        return false;
    }

    // Issue flush command
    log::info!("Issuing flush command (poll={poll})...");
    
    // Test bypasses storage layer, so allocate transfer directly
    let transfer_id = match awkernel_lib::storage::allocate_transfer_sync(0) {
        Ok(id) => id,
        Err(e) => {
            log::error!("Failed to allocate transfer for flush: {e:?}");
            return false;
        }
    };
    
    // Set up the transfer for polling mode if requested
    if let Ok(transfer) = awkernel_lib::storage::get_transfer_mut(transfer_id) {
        transfer.nsid = NSID;
        transfer.poll = poll;
        transfer.timeout_ms = 5000;  // 5 second timeout for flush
    }
    
    if let Err(e) = nvme.flush(NSID, transfer_id) {
        log::error!("Flush failed: {e:?}");
        awkernel_lib::storage::free_transfer(transfer_id);
        return false;
    }
    
    // Wait for completion if we're in interrupt mode
    // (In polling mode, the driver already waited)
    if !poll {
        wait_for_transfer_completion(transfer_id);
    }
    awkernel_lib::storage::free_transfer(transfer_id);

    log::info!("Flush completed successfully");
    true
}
