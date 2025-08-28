#![no_std]

extern crate alloc;

use alloc::{borrow::Cow, format, vec};
use awkernel_async_lib::task::spawn;
use awkernel_lib::{
    delay::uptime,
    storage::{self, StorageDeviceType},
};
use core::sync::atomic::{AtomicBool, AtomicU64, AtomicUsize, Ordering};
use log::{error, info, warn};

// Test configuration constants
const SMALL_BLOCK_SIZE: usize = 512; // Minimum block size
const MEDIUM_BLOCK_SIZE: usize = 4096; // 4KB - typical page size
const LARGE_BLOCK_SIZE: usize = 32768; // 32KB - large transfer
const MEGA_BLOCK_SIZE: usize = 65536; // 128 blocks * 512 bytes = 64KB

// Number of operations for different test scenarios
const QUICK_TEST_OPS: usize = 10; // Balance between measurement accuracy and speed
const NORMAL_TEST_OPS: usize = 20; // More operations for thorough testing

// Concurrent task counts
const LOW_CONCURRENCY: usize = 2;
const MEDIUM_CONCURRENCY: usize = 4;
// const HIGH_CONCURRENCY: usize = 64; // Commented out as unused

// Global statistics
static TOTAL_READS: AtomicU64 = AtomicU64::new(0);
static TOTAL_WRITES: AtomicU64 = AtomicU64::new(0);
static TOTAL_BYTES_READ: AtomicU64 = AtomicU64::new(0);
static TOTAL_BYTES_WRITTEN: AtomicU64 = AtomicU64::new(0);
static TOTAL_ERRORS: AtomicU64 = AtomicU64::new(0);
static TEST_PASSED: AtomicBool = AtomicBool::new(false);

// Concurrent test synchronization
static CONCURRENT_TASKS_SPAWNED: AtomicUsize = AtomicUsize::new(0);
static CONCURRENT_TASKS_COMPLETED: AtomicUsize = AtomicUsize::new(0);
static CONCURRENT_OPS_COMPLETED: AtomicU64 = AtomicU64::new(0);
static CONCURRENT_BYTES_TRANSFERRED: AtomicU64 = AtomicU64::new(0);

struct TestStats {
    operations: u64,
    bytes_transferred: u64,
    duration_ms: u64,
    errors: u64,
}

impl TestStats {
    fn new() -> Self {
        Self {
            operations: 0,
            bytes_transferred: 0,
            duration_ms: 0,
            errors: 0,
        }
    }

    fn throughput_mbps(&self) -> f32 {
        if self.duration_ms == 0 {
            return 0.0;
        }
        (self.bytes_transferred as f32 / 1024.0 / 1024.0) / (self.duration_ms as f32 / 1000.0)
    }

    fn iops(&self) -> f32 {
        if self.duration_ms == 0 {
            return 0.0;
        }
        (self.operations as f32) / (self.duration_ms as f32 / 1000.0)
    }

    fn avg_latency_ms(&self) -> f32 {
        if self.operations == 0 {
            return 0.0;
        }
        self.duration_ms as f32 / self.operations as f32
    }
}

pub async fn run() -> Result<(), alloc::borrow::Cow<'static, str>> {
    info!("=== Starting Storage Load Test ===");

    // Initialize storage transfer pool
    storage::init_transfer_pool();

    // Wait for storage devices to initialize
    awkernel_lib::delay::wait_millisec(2000);

    // Get available storage devices
    let devices = storage::get_all_storage_statuses();
    if devices.is_empty() {
        error!("No storage devices available for testing");
        return Err("No storage devices found".into());
    }

    info!("Found {} storage device(s)", devices.len());
    for device in &devices {
        info!(
            "  Device {}: {} ({:?})",
            device.interface_id, device.device_name, device.device_type
        );
    }

    // Select first NVMe device for testing, or fall back to any device
    let test_device = devices
        .iter()
        .find(|d| matches!(d.device_type, StorageDeviceType::NVMe))
        .or_else(|| devices.first())
        .unwrap();

    let device_id = test_device.interface_id;
    let block_size = test_device.block_size;

    info!(
        "Using device {} for load testing (block size: {} bytes)",
        test_device.device_name, block_size
    );

    // Run test suite
    let mut all_passed = true;

    // Skip slow sequential tests to focus on concurrent test
    // Test 1: Sequential Read Performance
    info!("\n=== Test 1: Sequential Read Performance ===");
    if !test_sequential_reads(device_id, block_size).await {
        all_passed = false;
    }

    // Test 2: Sequential Write Performance
    info!("\n=== Test 2: Sequential Write Performance ===");
    if !test_sequential_writes(device_id, block_size).await {
        all_passed = false;
    }

    // Test 3: Random Access Pattern
    info!("\n=== Test 3: Random Access Pattern ===");
    if !test_random_access(device_id, block_size).await {
        all_passed = false;
    }

    // Test 4: Mixed Read/Write Workload
    info!("\n=== Test 4: Mixed Read/Write Workload ===");
    if !test_mixed_workload(device_id, block_size).await {
        all_passed = false;
    }

    // Test 5: Concurrent I/O Operations
    info!("\n=== Test 5: Concurrent I/O Operations ===");
    if !test_concurrent_io(device_id, block_size).await {
        all_passed = false;
    }

    // Test 6: Large Block Transfers - Testing data corruption issue
    info!("\n=== Test 6: Large Block Transfers ===");
    if !test_large_blocks(device_id, block_size).await {
        all_passed = false;
    }

    // Test 7: Sustained Load Test
    info!("\n=== Test 7: Sustained Load Test ===");
    if !test_sustained_load(device_id, block_size).await {
        all_passed = false;
    }
    // Print final statistics
    print_final_stats();

    if all_passed {
        TEST_PASSED.store(true, Ordering::SeqCst);
        info!("\n=== All Storage Load Tests PASSED ===");
    } else {
        error!("\n=== Some Storage Load Tests FAILED ===");
    }

    Ok(())
}

async fn test_sequential_reads(device_id: u64, block_size: usize) -> bool {
    info!("Testing sequential read performance...");

    let test_sizes = [
        (SMALL_BLOCK_SIZE, "512B"),
        (MEDIUM_BLOCK_SIZE, "4KB"),
        (LARGE_BLOCK_SIZE, "32KB"),
    ];

    for (size, desc) in &test_sizes {
        let blocks = size / block_size;
        if blocks == 0 {
            continue; // Skip if test size is smaller than device block size
        }

        info!("  Testing with {desc} blocks...");
        let mut stats = TestStats::new();
        let start = uptime() / 1000;

        // Perform sequential reads
        let mut lba = 0u64;
        let mut buffer = vec![0u8; *size];

        for _ in 0..QUICK_TEST_OPS {
            match storage::async_read_block(device_id, lba, &mut buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += buffer.len() as u64;
                    TOTAL_READS.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_READ.fetch_add(buffer.len() as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("    Read failed at LBA {lba}: {e:?}");
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }

            // Move to next sequential position
            lba = (lba + blocks as u64) % 1000; // Wrap around at block 1000
        }

        stats.duration_ms = (uptime() / 1000) - start;

        info!(
            "    {} reads: {:.2} MB/s, {:.0} IOPS, {:.2}ms avg latency",
            desc,
            stats.throughput_mbps(),
            stats.iops(),
            stats.avg_latency_ms()
        );

        if stats.errors > 0 {
            error!("    {} errors occurred", stats.errors);
            return false;
        }
    }

    true
}

async fn test_sequential_writes(device_id: u64, block_size: usize) -> bool {
    info!("Testing sequential write performance...");

    let test_sizes = [
        (SMALL_BLOCK_SIZE, "512B"),
        (MEDIUM_BLOCK_SIZE, "4KB"),
        (LARGE_BLOCK_SIZE, "32KB"),
    ];

    // Use safe area for writes (avoid boot sectors)
    let start_lba = 1000u64;

    for (size, desc) in &test_sizes {
        let blocks = size / block_size;
        if blocks == 0 {
            continue;
        }

        info!("  Testing with {desc} blocks...");
        let mut stats = TestStats::new();
        let start = uptime() / 1000;

        // Create test pattern
        let mut buffer = vec![0u8; *size];
        for (i, byte) in buffer.iter_mut().enumerate() {
            *byte = (i & 0xFF) as u8;
        }

        let mut lba = start_lba;

        for _ in 0..QUICK_TEST_OPS {
            match storage::async_write_block(device_id, lba, &buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += buffer.len() as u64;
                    TOTAL_WRITES.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_WRITTEN.fetch_add(buffer.len() as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("    Write failed at LBA {lba}: {e:?}");
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }

            lba = start_lba + ((lba - start_lba + blocks as u64) % 1000);
        }

        stats.duration_ms = (uptime() / 1000) - start;

        info!(
            "    {} writes: {:.2} MB/s, {:.0} IOPS, {:.2}ms avg latency",
            desc,
            stats.throughput_mbps(),
            stats.iops(),
            stats.avg_latency_ms()
        );

        if stats.errors > 0 {
            error!("    {} errors occurred", stats.errors);
            return false;
        }
    }

    true
}

async fn test_random_access(device_id: u64, block_size: usize) -> bool {
    info!("Testing random access pattern...");

    let mut stats = TestStats::new();
    let start = uptime() / 1000;

    let mut buffer = vec![0u8; block_size];
    let max_lba = 2000u64; // Test within first 2000 blocks

    // Simple pseudo-random number generator
    let mut seed = 12345u64;

    for i in 0..NORMAL_TEST_OPS {
        // Generate pseudo-random LBA
        seed = (seed * 1103515245 + 12345) & 0x7fffffff;
        let lba = seed % max_lba;

        // Alternate between reads and writes
        let is_read = (i % 2) == 0;

        if is_read {
            match storage::async_read_block(device_id, lba, &mut buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += buffer.len() as u64;
                    TOTAL_READS.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_READ.fetch_add(buffer.len() as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("  Random read failed at LBA {lba}: {e:?}");
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        } else {
            // Fill buffer with test pattern
            for (j, byte) in buffer.iter_mut().enumerate() {
                *byte = ((lba + j as u64) & 0xFF) as u8;
            }

            match storage::async_write_block(device_id, lba, &buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += buffer.len() as u64;
                    TOTAL_WRITES.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_WRITTEN.fetch_add(buffer.len() as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("  Random write failed at LBA {lba}: {e:?}");
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    }

    stats.duration_ms = (uptime() / 1000) - start;

    info!(
        "  Random access: {:.2} MB/s, {:.0} IOPS, {:.2}ms avg latency",
        stats.throughput_mbps(),
        stats.iops(),
        stats.avg_latency_ms()
    );

    if stats.errors > 0 {
        error!("  {} errors occurred", stats.errors);
        return false;
    }

    true
}

async fn test_mixed_workload(device_id: u64, block_size: usize) -> bool {
    info!("Testing mixed read/write workload (70% read, 30% write)...");

    let mut stats = TestStats::new();
    let start = uptime() / 1000;

    let mut read_buffer = vec![0u8; MEDIUM_BLOCK_SIZE];
    let mut write_buffer = vec![0u8; MEDIUM_BLOCK_SIZE];

    // Fill write buffer with pattern
    for (i, byte) in write_buffer.iter_mut().enumerate() {
        *byte = (i & 0xFF) as u8;
    }

    let blocks = MEDIUM_BLOCK_SIZE / block_size;
    let safe_lba = 2000u64; // Start from safe area

    for i in 0..NORMAL_TEST_OPS {
        // 70% reads, 30% writes
        let is_read = (i % 10) < 7;
        let lba = safe_lba + (i as u64 % 100) * blocks as u64;

        if is_read {
            match storage::async_read_block(device_id, lba, &mut read_buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += read_buffer.len() as u64;
                    TOTAL_READS.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_READ.fetch_add(read_buffer.len() as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("  Mixed read failed at LBA {lba}: {e:?}");
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        } else {
            match storage::async_write_block(device_id, lba, &write_buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += write_buffer.len() as u64;
                    TOTAL_WRITES.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_WRITTEN.fetch_add(write_buffer.len() as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("  Mixed write failed at LBA {lba}: {e:?}");
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    }

    stats.duration_ms = (uptime() / 1000) - start;

    info!(
        "  Mixed workload: {:.2} MB/s, {:.0} IOPS, {:.2}ms avg latency",
        stats.throughput_mbps(),
        stats.iops(),
        stats.avg_latency_ms()
    );

    if stats.errors > 0 {
        error!("  {} errors occurred", stats.errors);
        return false;
    }

    true
}

async fn test_concurrent_io(device_id: u64, block_size: usize) -> bool {
    info!("Testing concurrent I/O operations...");

    let concurrency_levels = [(LOW_CONCURRENCY, "Low"), (MEDIUM_CONCURRENCY, "Medium")];

    for (num_tasks, desc) in &concurrency_levels {
        info!("  Testing with {desc} concurrency ({num_tasks} tasks)...");

        // Reset counters for this test
        CONCURRENT_TASKS_SPAWNED.store(0, Ordering::SeqCst);
        CONCURRENT_TASKS_COMPLETED.store(0, Ordering::SeqCst);
        CONCURRENT_OPS_COMPLETED.store(0, Ordering::SeqCst);
        CONCURRENT_BYTES_TRANSFERRED.store(0, Ordering::SeqCst);

        // Ensure each task has at least 2 operations
        let ops_per_task = core::cmp::max(2, QUICK_TEST_OPS / num_tasks);

        let start = uptime() / 1000;

        // Spawn concurrent tasks
        for task_id in 0..*num_tasks {
            let task_name = format!("io_task_{task_id}").into();
            CONCURRENT_TASKS_SPAWNED.fetch_add(1, Ordering::SeqCst);
            spawn(
                task_name,
                concurrent_io_task(device_id, block_size, task_id, ops_per_task),
                awkernel_async_lib::scheduler::SchedulerType::FIFO,
            );
        }

        // Wait for all tasks to complete by polling the completion counter
        let mut wait_iterations = 0;
        loop {
            let completed = CONCURRENT_TASKS_COMPLETED.load(Ordering::SeqCst);
            if completed >= *num_tasks {
                break;
            }

            // Short delay to avoid busy-waiting too aggressively
            awkernel_lib::delay::wait_millisec(10);
            wait_iterations += 1;

            // Timeout after 30 seconds (3000 iterations of 10ms)
            if wait_iterations > 3000 {
                error!("    Timeout waiting for concurrent tasks to complete");
                return false;
            }
        }

        let duration_ms = (uptime() / 1000) - start;
        let total_ops = CONCURRENT_OPS_COMPLETED.load(Ordering::SeqCst);
        let total_bytes = CONCURRENT_BYTES_TRANSFERRED.load(Ordering::SeqCst);

        if duration_ms > 0 {
            let throughput = (total_bytes as f32 / 1024.0 / 1024.0) / (duration_ms as f32 / 1000.0);
            let iops = total_ops as f32 / (duration_ms as f32 / 1000.0);
            info!(
                "    {desc} concurrency: {throughput:.2} MB/s, {iops:.0} IOPS, {} ops in {}ms",
                total_ops, duration_ms
            );
        } else {
            info!("    {desc} concurrency: completed too quickly to measure");
        }
    }

    true
}

async fn concurrent_io_task(
    device_id: u64,
    block_size: usize,
    task_id: usize,
    num_ops: usize,
) -> Result<(), Cow<'static, str>> {
    // Each task performs its I/O operations sequentially,
    // but multiple tasks run concurrently to achieve parallelism

    let base_lba = 1000u64 + (task_id as u64 * 100);
    let mut local_ops = 0u64;
    let mut local_bytes = 0u64;

    // Each task does its operations - the concurrency comes from multiple tasks
    for i in 0..num_ops {
        let lba = base_lba + (i as u64 % 100);

        if (i % 2) == 0 {
            // Read operation
            let mut buffer = vec![0u8; block_size];
            match storage::async_read_block(device_id, lba, &mut buffer).await {
                Ok(()) => {
                    local_ops += 1;
                    local_bytes += block_size as u64;
                    TOTAL_READS.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_READ.fetch_add(block_size as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("Concurrent read failed at LBA {lba}: {e:?}");
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        } else {
            // Write operation
            let mut buffer = vec![0u8; block_size];
            for (j, byte) in buffer.iter_mut().enumerate() {
                *byte = ((task_id + j) & 0xFF) as u8;
            }

            match storage::async_write_block(device_id, lba, &buffer).await {
                Ok(()) => {
                    local_ops += 1;
                    local_bytes += block_size as u64;
                    TOTAL_WRITES.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_WRITTEN.fetch_add(block_size as u64, Ordering::Relaxed);
                }
                Err(e) => {
                    error!("Concurrent write failed at LBA {lba}: {e:?}");
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        }
    }

    // Update global counters
    CONCURRENT_OPS_COMPLETED.fetch_add(local_ops, Ordering::SeqCst);
    CONCURRENT_BYTES_TRANSFERRED.fetch_add(local_bytes, Ordering::SeqCst);

    // Mark task as completed
    CONCURRENT_TASKS_COMPLETED.fetch_add(1, Ordering::SeqCst);

    Ok(())
}

async fn test_large_blocks(device_id: u64, block_size: usize) -> bool {
    info!("Testing large block transfers...");

    // Test with 64KB blocks (MAXPHYS limit)
    let large_size = MEGA_BLOCK_SIZE;
    let blocks = large_size / block_size;

    info!(
        "  Block size: {}, transfer size: {}, blocks: {}",
        block_size, large_size, blocks
    );

    if blocks == 0 {
        warn!("  Block size too large for device, skipping");
        return true;
    }

    let mut stats = TestStats::new();
    let start = uptime() / 1000;

    let mut buffer = vec![0u8; large_size];
    let safe_lba = 2000u64; // Use LBA within disk range (2MB disk = 4096 blocks)

    // Perform fewer operations due to larger size
    let num_ops = 1; // Just one operation for debugging

    for i in 0..num_ops {
        let lba = safe_lba + (i as u64 * blocks as u64);

        // Write test
        for (j, byte) in buffer.iter_mut().enumerate() {
            *byte = ((i + j) & 0xFF) as u8;
        }

        info!(
            "  Writing {} bytes to LBA {} ({} blocks)",
            buffer.len(),
            lba,
            blocks
        );
        match storage::async_write_block(device_id, lba, &buffer).await {
            Ok(()) => {
                stats.operations += 1;
                stats.bytes_transferred += buffer.len() as u64;
                TOTAL_WRITES.fetch_add(1, Ordering::Relaxed);
                TOTAL_BYTES_WRITTEN.fetch_add(buffer.len() as u64, Ordering::Relaxed);
            }
            Err(e) => {
                error!("  Large write failed at LBA {lba}: {e:?}");
                stats.errors += 1;
                TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
            }
        }

        // Read back and verify
        let mut read_buffer = vec![0u8; large_size];
        match storage::async_read_block(device_id, lba, &mut read_buffer).await {
            Ok(()) => {
                stats.operations += 1;
                stats.bytes_transferred += read_buffer.len() as u64;
                TOTAL_READS.fetch_add(1, Ordering::Relaxed);
                TOTAL_BYTES_READ.fetch_add(read_buffer.len() as u64, Ordering::Relaxed);

                // Verify data
                let mut mismatches = 0;
                let mut first_mismatch = None;
                for (j, (expected, actual)) in buffer.iter().zip(read_buffer.iter()).enumerate() {
                    if expected != actual {
                        if first_mismatch.is_none() {
                            first_mismatch = Some(j);
                        }
                        mismatches += 1;
                        if mismatches <= 5 {
                            error!("    Data mismatch at offset {j} (0x{j:x}): expected 0x{expected:02x}, got 0x{actual:02x}");
                        }
                    }
                }
                if mismatches > 0 {
                    error!(
                        "    Total {mismatches} bytes mismatched out of {} bytes",
                        large_size
                    );
                    if let Some(offset) = first_mismatch {
                        error!(
                            "    First mismatch at offset {} (0x{:x}), block boundary: {}",
                            offset,
                            offset,
                            offset / block_size
                        );
                    }
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
            Err(e) => {
                error!("  Large read failed at LBA {lba}: {e:?}");
                stats.errors += 1;
                TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
            }
        }
    }

    stats.duration_ms = (uptime() / 1000) - start;

    info!(
        "  Large blocks (64KB): {:.2} MB/s, {:.0} IOPS, {:.2}ms avg latency",
        stats.throughput_mbps(),
        stats.iops(),
        stats.avg_latency_ms()
    );

    if stats.errors > 0 {
        error!("  {} errors occurred", stats.errors);
        return false;
    }

    true
}

async fn test_sustained_load(device_id: u64, block_size: usize) -> bool {
    info!("Testing sustained load (2 seconds)...");

    let duration_ms = 2000u64; // 2 seconds - reduced for faster testing
    let start = uptime() / 1000;
    let mut stats = TestStats::new();

    let mut read_buffer = vec![0u8; MEDIUM_BLOCK_SIZE];
    let mut write_buffer = vec![0u8; MEDIUM_BLOCK_SIZE];

    // Fill write buffer
    for (i, byte) in write_buffer.iter_mut().enumerate() {
        *byte = (i & 0xFF) as u8;
    }

    let blocks = MEDIUM_BLOCK_SIZE / block_size;
    let safe_lba = 3000u64; // Use LBA within disk range
    let mut operation_count = 0u64;

    // Run for specified duration
    while (uptime() / 1000) - start < duration_ms {
        let lba = safe_lba + (operation_count % 1000) * blocks as u64;

        // Alternate operations
        if (operation_count % 3) == 0 {
            // Write
            match storage::async_write_block(device_id, lba, &write_buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += write_buffer.len() as u64;
                    TOTAL_WRITES.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_WRITTEN.fetch_add(write_buffer.len() as u64, Ordering::Relaxed);
                }
                Err(_) => {
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        } else {
            // Read
            match storage::async_read_block(device_id, lba, &mut read_buffer).await {
                Ok(()) => {
                    stats.operations += 1;
                    stats.bytes_transferred += read_buffer.len() as u64;
                    TOTAL_READS.fetch_add(1, Ordering::Relaxed);
                    TOTAL_BYTES_READ.fetch_add(read_buffer.len() as u64, Ordering::Relaxed);
                }
                Err(_) => {
                    stats.errors += 1;
                    TOTAL_ERRORS.fetch_add(1, Ordering::Relaxed);
                }
            }
        }

        operation_count += 1;

        // Check every 100 operations if we should continue
        if operation_count % 100 == 0 {
            let elapsed = (uptime() / 1000) - start;
            if elapsed >= duration_ms {
                break;
            }
        }
    }

    stats.duration_ms = (uptime() / 1000) - start;

    info!("  Sustained load results:");
    info!("    Duration: {}ms", stats.duration_ms);
    info!("    Operations: {}", stats.operations);
    info!("    Throughput: {:.2} MB/s", stats.throughput_mbps());
    info!("    IOPS: {:.0}", stats.iops());
    info!("    Average latency: {:.2}ms", stats.avg_latency_ms());

    if stats.errors > 0 {
        error!(
            "    {} errors occurred ({:.2}% error rate)",
            stats.errors,
            (stats.errors as f32 / stats.operations as f32) * 100.0
        );
        // Allow up to 1% error rate for sustained load
        if stats.errors > stats.operations / 100 {
            return false;
        }
    }

    true
}

fn print_final_stats() {
    info!("\n=== Final Statistics ===");

    let total_reads = TOTAL_READS.load(Ordering::Relaxed);
    let total_writes = TOTAL_WRITES.load(Ordering::Relaxed);
    let total_bytes_read = TOTAL_BYTES_READ.load(Ordering::Relaxed);
    let total_bytes_written = TOTAL_BYTES_WRITTEN.load(Ordering::Relaxed);
    let total_errors = TOTAL_ERRORS.load(Ordering::Relaxed);

    let total_ops = total_reads + total_writes;
    info!("Total Operations: {total_ops}");
    let read_mb = total_bytes_read as f32 / 1024.0 / 1024.0;
    info!("  Reads:  {total_reads} ({read_mb:.1} MB)");
    let write_mb = total_bytes_written as f32 / 1024.0 / 1024.0;
    info!("  Writes: {total_writes} ({write_mb:.1} MB)");
    let total_mb = (total_bytes_read + total_bytes_written) as f32 / 1024.0 / 1024.0;
    info!("Total Data Transferred: {total_mb:.1} MB");
    info!("Total Errors: {total_errors}");

    if total_errors > 0 && total_ops > 0 {
        let error_rate = (total_errors as f32 / total_ops as f32) * 100.0;
        info!("Error Rate: {error_rate:.3}%");
    }
}

pub fn test_completed() -> bool {
    TEST_PASSED.load(Ordering::SeqCst)
}
