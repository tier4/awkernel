#![no_std]

extern crate alloc;

use awkernel_lib::{
    addr::Addr,
    dma_pool::DMAPool, 
    paging::PAGESIZE
};
use core::sync::atomic::{AtomicBool, Ordering};

// Import NVMe types
use awkernel_drivers::pcie::{nvme::NVME_DEVICE, PCIeDevice};

static TEST_PASSED: AtomicBool = AtomicBool::new(false);

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
    /*
    if !test_read_write_mode(true).await {
        log::error!("Test B (Read/Write - Polling) FAILED");
        return;
    }
    log::info!("Test B (Read/Write - Polling) PASSED");
    */
    
    // Test B2: Read/Write Test (Interrupt Mode)
    if !test_read_write_mode(false).await {
        log::error!("Test B2 (Read/Write - Interrupt) FAILED");
        return;
    }
    log::info!("Test B2 (Read/Write - Interrupt) PASSED");
    
    // Test C: Flush Test (Polling Mode)
    // Commented out to isolate interrupt test
    /*
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
    */
    
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
    let write_phys = write_dma.get_phy_addr().as_usize() as u64;
    
    // Write data
    log::info!("Writing {TEST_BLOCKS} blocks to LBA {TEST_LBA} (poll={poll})...");
    if let Err(e) = nvme.write_sectors(NSID, TEST_LBA, TEST_BLOCKS, write_phys, poll) {
        log::error!("Write failed: {e:?}");
        return false;
    }
    log::info!("Write completed successfully");
    
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
    let read_phys = read_dma.get_phy_addr().as_usize() as u64;
    
    // Read data back
    log::info!("Reading {TEST_BLOCKS} blocks from LBA {TEST_LBA} (poll={poll})...");
    if let Err(e) = nvme.read_sectors(NSID, TEST_LBA, TEST_BLOCKS, read_phys, poll) {
        log::error!("Read failed: {e:?}");
        return false;
    }
    log::info!("Read completed successfully");
    
    // Verify data
    log::info!("Verifying data...");
    let mut mismatches = 0;
    for (i, &actual) in read_slice.iter().enumerate().take(buffer_size) {
        let expected = ((i % 256) as u8) ^ 0xAA;
        if expected != actual {
            if mismatches < 10 {
                log::error!("Data mismatch at offset {i}: expected 0x{expected:02x}, got 0x{actual:02x}");
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
    let write_phys = write_dma.get_phy_addr().as_usize() as u64;
    
    // Write data
    log::info!("Writing data before flush (poll={poll})...");
    if let Err(e) = nvme.write_sectors(NSID, TEST_LBA, TEST_BLOCKS, write_phys, poll) {
        log::error!("Write before flush failed: {e:?}");
        return false;
    }
    
    // Issue flush command
    log::info!("Issuing flush command (poll={poll})...");
    if let Err(e) = nvme.flush(NSID, poll) {
        log::error!("Flush failed: {e:?}");
        return false;
    }
    
    log::info!("Flush completed successfully");
    true
}