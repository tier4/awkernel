#[cfg(not(feature = "std"))]
use alloc::collections::{
    btree_map::Entry,
    BTreeMap, BTreeSet,
};
#[cfg(not(feature = "std"))]
use core::sync::atomic::{AtomicU16, Ordering};

#[cfg(not(feature = "std"))]
use crate::sync::{mcs::MCSNode, mutex::Mutex};

#[cfg(not(feature = "std"))]
use super::tcp::TcpPort;

#[allow(dead_code)]
pub(super) struct PortAllocator {
    #[cfg(not(feature = "std"))]
    tcp_ipv4: Mutex<BTreeMap<u16, u64>>,
    #[cfg(not(feature = "std"))]
    tcp_ipv4_ephemeral: AtomicU16,
    #[cfg(not(feature = "std"))]
    tcp_ipv6: Mutex<BTreeMap<u16, u64>>,
    #[cfg(not(feature = "std"))]
    tcp_ipv6_ephemeral: AtomicU16,
    #[cfg(not(feature = "std"))]
    udp_ipv4: Mutex<BTreeSet<u16>>,
    #[cfg(not(feature = "std"))]
    udp_ipv4_ephemeral: AtomicU16,
    #[cfg(not(feature = "std"))]
    udp_ipv6: Mutex<BTreeSet<u16>>,
    #[cfg(not(feature = "std"))]
    udp_ipv6_ephemeral: AtomicU16,
}

#[allow(dead_code)]
pub(super) static PORT_ALLOC: PortAllocator = PortAllocator::new();

impl PortAllocator {
    pub(super) const fn new() -> Self {
        Self {
            #[cfg(not(feature = "std"))]
            tcp_ipv4: Mutex::new(BTreeMap::new()),
            #[cfg(not(feature = "std"))]
            tcp_ipv4_ephemeral: AtomicU16::new(u16::MAX >> 2),
            #[cfg(not(feature = "std"))]
            tcp_ipv6: Mutex::new(BTreeMap::new()),
            #[cfg(not(feature = "std"))]
            tcp_ipv6_ephemeral: AtomicU16::new(u16::MAX >> 2),
            #[cfg(not(feature = "std"))]
            udp_ipv4: Mutex::new(BTreeSet::new()),
            #[cfg(not(feature = "std"))]
            udp_ipv4_ephemeral: AtomicU16::new(u16::MAX >> 2),
            #[cfg(not(feature = "std"))]
            udp_ipv6: Mutex::new(BTreeSet::new()),
            #[cfg(not(feature = "std"))]
            udp_ipv6_ephemeral: AtomicU16::new(u16::MAX >> 2),
        }
    }

    /// Allocate an ephemeral TCP IPv4 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn get_ephemeral_tcp_ipv4(&self) -> Option<TcpPort> {
        let cursor = self.tcp_ipv4_ephemeral.load(Ordering::Relaxed);
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv4.lock(&mut node);
        for i in 0..(u16::MAX >> 2) {
            let port = cursor.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };
            if let Entry::Vacant(e) = map.entry(port) {
                e.insert(1);
                self.tcp_ipv4_ephemeral.store(port, Ordering::Relaxed);
                return Some(TcpPort::new(port, true));
            }
        }
        None
    }

    /// Claim a specific TCP IPv4 port. Returns `None` if the port is already in use.
    #[cfg(not(feature = "std"))]
    pub(super) fn try_claim_tcp_ipv4(&self, port: u16) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv4.lock(&mut node);
        if map.contains_key(&port) {
            None
        } else {
            map.insert(port, 1);
            Some(TcpPort::new(port, true))
        }
    }

    /// Increment the reference count for a TCP IPv4 port (used by `TcpListener::accept`).
    #[cfg(not(feature = "std"))]
    pub(super) fn increment_ref_tcp_ipv4(&self, port: u16) -> TcpPort {
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv4.lock(&mut node);
        if let Some(e) = map.get_mut(&port) {
            *e += 1;
        } else {
            map.insert(port, 1);
        }
        TcpPort::new(port, true)
    }

    /// Decrement the reference count for a TCP IPv4 port, freeing it when it reaches zero.
    #[cfg(not(feature = "std"))]
    pub(super) fn decrement_ref_tcp_ipv4(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv4.lock(&mut node);
        if let Some(e) = map.get_mut(&port) {
            *e -= 1;
            if *e == 0 {
                map.remove(&port);
            }
        }
    }

    /// Allocate an ephemeral TCP IPv6 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn get_ephemeral_tcp_ipv6(&self) -> Option<TcpPort> {
        let cursor = self.tcp_ipv6_ephemeral.load(Ordering::Relaxed);
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv6.lock(&mut node);
        for i in 0..(u16::MAX >> 2) {
            let port = cursor.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };
            if let Entry::Vacant(e) = map.entry(port) {
                e.insert(1);
                self.tcp_ipv6_ephemeral.store(port, Ordering::Relaxed);
                return Some(TcpPort::new(port, false));
            }
        }
        None
    }

    /// Claim a specific TCP IPv6 port. Returns `None` if the port is already in use.
    #[cfg(not(feature = "std"))]
    pub(super) fn try_claim_tcp_ipv6(&self, port: u16) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv6.lock(&mut node);
        if map.contains_key(&port) {
            None
        } else {
            map.insert(port, 1);
            Some(TcpPort::new(port, false))
        }
    }

    /// Increment the reference count for a TCP IPv6 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn increment_ref_tcp_ipv6(&self, port: u16) -> TcpPort {
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv6.lock(&mut node);
        if let Some(e) = map.get_mut(&port) {
            *e += 1;
        } else {
            map.insert(port, 1);
        }
        TcpPort::new(port, false)
    }

    /// Decrement the reference count for a TCP IPv6 port, freeing it when it reaches zero.
    #[cfg(not(feature = "std"))]
    pub(super) fn decrement_ref_tcp_ipv6(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut map = self.tcp_ipv6.lock(&mut node);
        if let Some(e) = map.get_mut(&port) {
            *e -= 1;
            if *e == 0 {
                map.remove(&port);
            }
        }
    }

    /// Allocate an ephemeral UDP IPv4 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn get_ephemeral_udp_ipv4(&self) -> Option<u16> {
        let cursor = self.udp_ipv4_ephemeral.load(Ordering::Relaxed);
        let mut node = MCSNode::new();
        let mut set = self.udp_ipv4.lock(&mut node);
        for i in 0..(u16::MAX >> 2) {
            let port = cursor.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };
            if set.insert(port) {
                self.udp_ipv4_ephemeral.store(port, Ordering::Relaxed);
                return Some(port);
            }
        }
        None
    }

    /// Claim a specific UDP IPv4 port. Returns `false` if the port is already in use.
    #[cfg(not(feature = "std"))]
    pub(super) fn try_claim_udp_ipv4(&self, port: u16) -> bool {
        let mut node = MCSNode::new();
        let result = self.udp_ipv4.lock(&mut node).insert(port);
        result
    }

    /// Free a UDP IPv4 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn free_udp_ipv4(&self, port: u16) {
        let mut node = MCSNode::new();
        self.udp_ipv4.lock(&mut node).remove(&port);
    }

    /// Allocate an ephemeral UDP IPv6 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn get_ephemeral_udp_ipv6(&self) -> Option<u16> {
        let cursor = self.udp_ipv6_ephemeral.load(Ordering::Relaxed);
        let mut node = MCSNode::new();
        let mut set = self.udp_ipv6.lock(&mut node);
        for i in 0..(u16::MAX >> 2) {
            let port = cursor.wrapping_add(i);
            let port = if port == 0 { u16::MAX >> 2 } else { port };
            if set.insert(port) {
                self.udp_ipv6_ephemeral.store(port, Ordering::Relaxed);
                return Some(port);
            }
        }
        None
    }

    /// Claim a specific UDP IPv6 port. Returns `false` if the port is already in use.
    #[cfg(not(feature = "std"))]
    pub(super) fn try_claim_udp_ipv6(&self, port: u16) -> bool {
        let mut node = MCSNode::new();
        let result = self.udp_ipv6.lock(&mut node).insert(port);
        result
    }

    /// Free a UDP IPv6 port.
    #[cfg(not(feature = "std"))]
    pub(super) fn free_udp_ipv6(&self, port: u16) {
        let mut node = MCSNode::new();
        self.udp_ipv6.lock(&mut node).remove(&port);
    }
}
