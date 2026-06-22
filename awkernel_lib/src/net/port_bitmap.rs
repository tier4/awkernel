//! Bitmap-backed port sets for TCP/UDP local-port allocation.
//!
//! These pure data structures live outside the `port_alloc` module (which is
//! `#[cfg(not(feature = "std"))]` because it wires up the `TcpPort`/`UdpPort`
//! RAII handles and the MCS `Mutex`) so they can be unit-tested by the host
//! `--features std` test build, which does not compile `port_alloc`.
//!
//! The whole 16-bit port space is tracked in a fixed `[u64; 1024]` bitmap
//! (8 KiB), so claiming and releasing a port is allocation-free and a free
//! ephemeral port is found by scanning whole `u64` words (64 ports at a time).
//!
//! UDP ports have a single owner, so a plain bitmap suffices. TCP ports can be
//! shared (a `TcpListener` and every connection it accepts share the same local
//! port), so [`TcpPortSet`] keeps a small overflow map of reference counts for
//! the few ports whose count is `>= 2`; a port present only in the bitmap has
//! count `1`.
#![cfg(any(not(feature = "std"), test))]

use alloc::collections::BTreeMap;

/// First ephemeral port. Matches the previous allocator's first handed-out port
/// (`(u16::MAX >> 2) + 1`). It is word-aligned, so the ephemeral range
/// `[EPHEMERAL_MIN, u16::MAX]` is exactly the `u64` words `FIRST_WORD..NWORDS`.
const EPHEMERAL_MIN: u16 = (u16::MAX >> 2) + 1;

/// Number of `u64` words needed to cover all 65536 ports.
const NWORDS: usize = (u16::MAX as usize + 1) / 64;

/// Index of the first word in the ephemeral range.
const FIRST_WORD: usize = EPHEMERAL_MIN as usize / 64;

/// A bitmap over the full 16-bit port space. A set bit means the port is in use.
struct PortBitmap {
    bits: [u64; NWORDS],
}

impl PortBitmap {
    const fn new() -> Self {
        Self {
            bits: [0; NWORDS],
        }
    }

    #[inline]
    fn word_bit(port: u16) -> (usize, u64) {
        ((port >> 6) as usize, 1u64 << (port & 63))
    }

    /// Set the bit for `port`. Returns `true` if it was previously clear.
    fn set(&mut self, port: u16) -> bool {
        let (w, mask) = Self::word_bit(port);
        let was_set = self.bits[w] & mask != 0;
        self.bits[w] |= mask;
        !was_set
    }

    /// Clear the bit for `port`. Returns `true` if it was previously set.
    fn clear(&mut self, port: u16) -> bool {
        let (w, mask) = Self::word_bit(port);
        let was_set = self.bits[w] & mask != 0;
        self.bits[w] &= !mask;
        was_set
    }

    #[cfg(test)]
    fn test(&self, port: u16) -> bool {
        let (w, mask) = Self::word_bit(port);
        self.bits[w] & mask != 0
    }

    /// Find a free port in the ephemeral range, scanning whole words starting
    /// from the word containing `cursor` and wrapping around the range. Returns
    /// the lowest free port in the first non-full word found, or `None` if the
    /// ephemeral range is fully allocated.
    fn find_free_from(&self, cursor: u16) -> Option<u16> {
        let eph_words = NWORDS - FIRST_WORD;
        let start = (cursor as usize / 64).clamp(FIRST_WORD, NWORDS - 1) - FIRST_WORD;
        for i in 0..eph_words {
            let w = FIRST_WORD + (start + i) % eph_words;
            let word = self.bits[w];
            if word != u64::MAX {
                // `trailing_ones` is the index of the lowest zero bit.
                let bit = word.trailing_ones() as u16;
                return Some(((w as u16) << 6) | bit);
            }
        }
        None
    }
}

/// Bitmap-backed set of UDP ports (single owner per port).
pub(super) struct UdpPortSet {
    bitmap: PortBitmap,
    cursor: u16,
}

impl UdpPortSet {
    pub(super) const fn new() -> Self {
        Self {
            bitmap: PortBitmap::new(),
            cursor: EPHEMERAL_MIN,
        }
    }

    /// Allocate a free ephemeral port, or `None` if the range is exhausted.
    pub(super) fn alloc_ephemeral(&mut self) -> Option<u16> {
        let port = self.bitmap.find_free_from(self.cursor)?;
        self.bitmap.set(port);
        self.cursor = port;
        Some(port)
    }

    /// Claim a specific port. Returns `true` if it was free and is now claimed.
    pub(super) fn try_claim(&mut self, port: u16) -> bool {
        self.bitmap.set(port)
    }

    /// Release a port.
    pub(super) fn free(&mut self, port: u16) {
        self.bitmap.clear(port);
    }
}

/// Bitmap-backed set of TCP ports with reference counting.
///
/// A port present only in `bitmap` has count `1`; `overflow` holds the full
/// count for ports whose count is `>= 2`.
pub(super) struct TcpPortSet {
    bitmap: PortBitmap,
    overflow: BTreeMap<u16, u64>,
    cursor: u16,
}

impl TcpPortSet {
    pub(super) const fn new() -> Self {
        Self {
            bitmap: PortBitmap::new(),
            overflow: BTreeMap::new(),
            cursor: EPHEMERAL_MIN,
        }
    }

    /// Allocate a free ephemeral port with count `1`, or `None` if exhausted.
    pub(super) fn alloc_ephemeral(&mut self) -> Option<u16> {
        let port = self.bitmap.find_free_from(self.cursor)?;
        self.bitmap.set(port);
        self.cursor = port;
        Some(port)
    }

    /// Claim a specific port with count `1`. Returns `true` if it was free.
    pub(super) fn try_claim(&mut self, port: u16) -> bool {
        self.bitmap.set(port)
    }

    /// Increment the reference count for `port`, claiming it if currently free.
    pub(super) fn increment(&mut self, port: u16) {
        if self.bitmap.set(port) {
            // Was free: now count 1, tracked by the bitmap alone.
        } else if let Some(count) = self.overflow.get_mut(&port) {
            *count += 1;
        } else {
            // Was count 1 (bitmap only): promote to the overflow map at count 2.
            self.overflow.insert(port, 2);
        }
    }

    /// Decrement the reference count for `port`, releasing it when it reaches 0.
    pub(super) fn decrement(&mut self, port: u16) {
        if let Some(count) = self.overflow.get_mut(&port) {
            *count -= 1;
            if *count == 1 {
                // Back to count 1: tracked by the bitmap alone.
                self.overflow.remove(&port);
            }
        } else {
            // Count 1 (bitmap only) -> 0, or already free (clear is a no-op).
            self.bitmap.clear(port);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bitmap_set_clear_test() {
        let mut b = PortBitmap::new();
        assert!(!b.test(12345));
        assert!(b.set(12345)); // newly set
        assert!(b.test(12345));
        assert!(!b.set(12345)); // already set
        assert!(b.clear(12345)); // was set
        assert!(!b.test(12345));
        assert!(!b.clear(12345)); // already clear
        assert!(b.set(12345)); // re-set after clear
    }

    #[test]
    fn find_free_returns_ephemeral_port() {
        let b = PortBitmap::new();
        let p = b.find_free_from(EPHEMERAL_MIN).unwrap();
        assert!(p >= EPHEMERAL_MIN);
    }

    #[test]
    fn find_free_skips_full_word() {
        let mut b = PortBitmap::new();
        // Fill the first ephemeral word entirely (ports EPHEMERAL_MIN..+64).
        for port in EPHEMERAL_MIN..EPHEMERAL_MIN + 64 {
            assert!(b.set(port));
        }
        // The first free port must be the start of the next word.
        let p = b.find_free_from(EPHEMERAL_MIN).unwrap();
        assert_eq!(p, EPHEMERAL_MIN + 64);
    }

    #[test]
    fn udp_alloc_distinct_then_reuse() {
        let mut s = UdpPortSet::new();
        let a = s.alloc_ephemeral().unwrap();
        let b = s.alloc_ephemeral().unwrap();
        assert_ne!(a, b);
        assert!(a >= EPHEMERAL_MIN && b >= EPHEMERAL_MIN);

        // A duplicate claim is rejected while it is in use.
        assert!(!s.try_claim(a));

        // After freeing, the port can be claimed again.
        s.free(a);
        assert!(s.try_claim(a));
    }

    #[test]
    fn udp_try_claim_specific_port() {
        let mut s = UdpPortSet::new();
        assert!(s.try_claim(80));
        assert!(!s.try_claim(80));
        s.free(80);
        assert!(s.try_claim(80));
    }

    #[test]
    fn tcp_refcount_promote_and_demote() {
        let mut s = TcpPortSet::new();
        let port = s.alloc_ephemeral().unwrap(); // count 1, bitmap only
        assert!(s.overflow.is_empty());

        s.increment(port); // count 2 -> overflow
        assert_eq!(s.overflow.get(&port), Some(&2));
        s.increment(port); // count 3
        assert_eq!(s.overflow.get(&port), Some(&3));

        s.decrement(port); // count 2
        assert_eq!(s.overflow.get(&port), Some(&2));
        s.decrement(port); // count 1 -> overflow entry removed, bit kept
        assert!(s.overflow.is_empty());
        assert!(s.bitmap.test(port));

        s.decrement(port); // count 0 -> bit cleared
        assert!(!s.bitmap.test(port));
    }

    #[test]
    fn tcp_increment_on_free_port_claims_it() {
        let mut s = TcpPortSet::new();
        // increment on an absent port claims it at count 1 (matches the old
        // `increment_ref` inserting count 1 for an absent port).
        s.increment(700);
        assert!(s.bitmap.test(700));
        assert!(s.overflow.is_empty());

        // It is now in use, so a fresh claim is rejected.
        assert!(!s.try_claim(700));

        s.decrement(700);
        assert!(!s.bitmap.test(700));
    }

    #[test]
    fn tcp_try_claim_duplicate_rejected() {
        let mut s = TcpPortSet::new();
        assert!(s.try_claim(443));
        assert!(!s.try_claim(443));
    }

    #[test]
    fn ephemeral_range_exhaustion() {
        let mut s = UdpPortSet::new();
        let mut count = 0usize;
        while s.alloc_ephemeral().is_some() {
            count += 1;
        }
        // The ephemeral range is [EPHEMERAL_MIN, u16::MAX].
        assert_eq!(count, (u16::MAX - EPHEMERAL_MIN) as usize + 1);
        assert!(s.alloc_ephemeral().is_none());
    }
}
