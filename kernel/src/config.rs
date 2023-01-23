pub use crate::arch::config::*;

/// Heap size is 256MiB.
#[allow(dead_code)]
pub const HEAP_SIZE: u64 = 256 * 1024 * 1024;

#[cfg(test)]
#[allow(dead_code)]
pub const HEAP_START: u64 = 0;
