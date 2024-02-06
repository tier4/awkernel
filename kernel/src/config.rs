pub use crate::arch::config::*;

/// Backup Heap size is 64 MiB
#[allow(dead_code)]
pub const BACKUP_HEAP_SIZE: usize = 64 * 1024 * 1024;

#[cfg(test)]
#[allow(dead_code)]
pub const HEAP_START: usize = 0;

#[allow(dead_code)]
pub const DMA_SIZE: usize = 128 * 1024 * 1024; // 128MiB per NUMA node
