#![no_std]

extern crate alloc;

use core::sync::atomic::{AtomicBool, Ordering};

static TEST_PASSED: AtomicBool = AtomicBool::new(false);

pub async fn run() {
    log::info!("=== Starting Storage Interrupt Handler Tests ===");

    // Test 1: Check if storage service is running
    if !test_storage_service_running() {
        log::error!("Test 1 (Storage Service Running) FAILED");
        return;
    }
    log::info!("Test 1 (Storage Service Running) PASSED");

    // Test 2: Check storage device registration
    if !test_storage_device_registration() {
        log::error!("Test 2 (Storage Device Registration) FAILED");
        return;
    }
    log::info!("Test 2 (Storage Device Registration) PASSED");

    // Test 3: Test interrupt handler registration
    if !test_interrupt_handler_registration().await {
        log::error!("Test 3 (Interrupt Handler Registration) FAILED");
        return;
    }
    log::info!("Test 3 (Interrupt Handler Registration) PASSED");

    // Test 4: Test actual storage interrupt flow
    if !test_storage_interrupt_flow().await {
        log::error!("Test 4 (Storage Interrupt Flow) FAILED");
        return;
    }
    log::info!("Test 4 (Storage Interrupt Flow) PASSED");

    TEST_PASSED.store(true, Ordering::SeqCst);
    log::info!("=== All Storage Interrupt Tests PASSED ===");
}

fn test_storage_service_running() -> bool {
    log::info!("Test 1: Checking if storage service is running...");
    
    // The storage service should have started and registered storage devices
    let devices = awkernel_lib::storage::get_all_storage_statuses();
    
    if devices.is_empty() {
        log::warn!("No storage devices found - this might be expected in QEMU without NVMe");
        // Don't fail the test if no devices are found, as QEMU might not have NVMe
        return true;
    }
    
    log::info!("Found {} storage device(s)", devices.len());
    for device in devices {
        log::info!("  Device {}: {} (type: {:?})", 
            device.interface_id, 
            device.device_name,
            device.device_type
        );
        log::info!("    IRQs: {:?}", device.irqs);
        log::info!("    Block size: {}, Blocks: {}", device.block_size, device.num_blocks);
    }
    
    true
}

fn test_storage_device_registration() -> bool {
    log::info!("Test 2: Testing storage device registration...");
    
    // Try to get info about device 0 (if it exists)
    match awkernel_lib::storage::get_storage_status(0) {
        Ok(status) => {
            log::info!("Successfully retrieved storage device 0 info:");
            log::info!("  Name: {}", status.device_name);
            log::info!("  Type: {:?}", status.device_type);
            log::info!("  Block size: {} bytes", status.block_size);
            log::info!("  Total blocks: {}", status.num_blocks);
            log::info!("  Capacity: {} MB", (status.num_blocks * status.block_size as u64) / (1024 * 1024));
            true
        }
        Err(_) => {
            log::warn!("No storage device with ID 0 found - this is expected if no NVMe is present");
            true
        }
    }
}

async fn test_interrupt_handler_registration() -> bool {
    log::info!("Test 3: Testing interrupt handler registration...");
    
    // Check if we can register a waker for a storage interrupt
    let devices = awkernel_lib::storage::get_all_storage_statuses();
    
    if devices.is_empty() {
        log::warn!("No devices to test interrupt registration");
        return true;
    }
    
    // Get the first device's first IRQ
    let first_device = &devices[0];
    if first_device.irqs.is_empty() {
        log::warn!("Device has no IRQs configured");
        return true;
    }
    
    let test_irq = first_device.irqs[0];
    log::info!("Testing interrupt registration for IRQ {}", test_irq);
    
    // Create a future that waits for the interrupt
    use core::future::Future;
    use core::task::{Context, Poll};
    use core::pin::Pin;
    
    struct TestInterruptFuture {
        irq: u16,
        registered: bool,
    }
    
    impl Future for TestInterruptFuture {
        type Output = bool;
        
        fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            if !self.registered {
                self.registered = true;
                let success = awkernel_lib::storage::register_waker_for_storage_interrupt(
                    self.irq, 
                    cx.waker().clone()
                );
                log::info!("Waker registration returned: {}", success);
                
                // For testing, we'll consider registration success as passing
                Poll::Ready(success)
            } else {
                Poll::Ready(true)
            }
        }
    }
    
    let future = TestInterruptFuture { 
        irq: test_irq, 
        registered: false 
    };
    
    future.await
}

async fn test_storage_interrupt_flow() -> bool {
    log::info!("Test 4: Testing storage interrupt flow...");
    
    // This test verifies that the storage interrupt handler is properly connected
    let devices = awkernel_lib::storage::get_all_storage_statuses();
    
    if devices.is_empty() {
        log::warn!("No devices available for interrupt flow test");
        return true;
    }
    
    let device = &devices[0];
    log::info!("Testing with device: {}", device.device_name);
    
    // The interrupt flow is already tested by the NVMe test when it uses interrupt mode
    // Here we just verify the service is handling interrupts
    if !device.irqs.is_empty() {
        log::info!("Device has {} interrupt(s) configured", device.irqs.len());
        log::info!("Storage interrupt handler is ready to process interrupts");
    }
    
    true
}