//! Filesystem capabilities
//!
//! This module defines capabilities that filesystems can declare to indicate
//! their supported features and behaviors.

use bitflags::bitflags;

bitflags! {
    /// Capabilities that a filesystem can have
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct FsCapabilities: u32 {
        /// Filesystem is read-only
        const READONLY = 0x01;
        /// Filesystem is case-sensitive
        const CASE_SENSITIVE = 0x02;
        /// Filesystem supports Unicode filenames
        const UNICODE = 0x04;
        /// Filesystem data is persistent (survives reboot)
        const PERSISTENT = 0x08;
        /// Filesystem is network-based
        const NETWORK = 0x10;
        /// Filesystem supports extended attributes
        const EXTENDED_ATTRS = 0x20;
        /// Filesystem supports symbolic links
        const SYMLINKS = 0x40;
        /// Filesystem supports hard links
        const HARDLINKS = 0x80;
        /// Filesystem supports sparse files
        const SPARSE_FILES = 0x100;
        /// Filesystem supports file compression
        const COMPRESSION = 0x200;
        /// Filesystem supports file encryption
        const ENCRYPTION = 0x400;
        /// Filesystem supports access control lists
        const ACL = 0x800;
        /// Filesystem supports quotas
        const QUOTAS = 0x1000;
        /// Filesystem supports snapshots
        const SNAPSHOTS = 0x2000;
        /// Filesystem supports async operations
        const ASYNC_OPS = 0x4000;
    }
}

impl Default for FsCapabilities {
    fn default() -> Self {
        // Most filesystems support basic operations and are case-sensitive
        Self::CASE_SENSITIVE | Self::UNICODE | Self::ASYNC_OPS
    }
}

impl FsCapabilities {
    /// Create capabilities for a read-only filesystem
    pub const fn readonly() -> Self {
        Self::from_bits_truncate(Self::READONLY.bits() | Self::CASE_SENSITIVE.bits())
    }
    
    /// Create capabilities for an in-memory filesystem
    pub const fn memory() -> Self {
        Self::from_bits_truncate(
            Self::CASE_SENSITIVE.bits() | 
            Self::UNICODE.bits() | 
            Self::ASYNC_OPS.bits()
        )
    }
    
    /// Create capabilities for a typical FAT filesystem
    pub const fn fat() -> Self {
        Self::from_bits_truncate(
            Self::UNICODE.bits() | 
            Self::PERSISTENT.bits() |
            Self::ASYNC_OPS.bits()
            // Note: FAT is typically case-insensitive
        )
    }
}