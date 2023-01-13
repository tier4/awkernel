pub use crate::arch::config::*;

/// Heap size is 256MiB.
pub const HEAP_SIZE: u64 = 256 * 1024 * 1024;

#[cfg(test)]
pub const HEAP_START: u64 = 0;
