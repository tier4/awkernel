#![cfg(not(feature = "std"))]

use alloc::collections::{btree_map::Entry, BTreeMap, BTreeSet};

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::tcp::TcpPort;

/// RAII handle for a claimed UDP port. Frees the port from [`PORT_ALLOC`] on drop,
/// so the port is released on any error path between claiming it and constructing
/// the owning socket.
pub(super) struct UdpPort {
    port: u16,
    is_ipv4: bool,
}

impl UdpPort {
    pub(super) fn port(&self) -> u16 {
        self.port
    }
}

impl Drop for UdpPort {
    fn drop(&mut self) {
        if self.is_ipv4 {
            PORT_ALLOC.free_udp_ipv4(self.port);
        } else {
            PORT_ALLOC.free_udp_ipv6(self.port);
        }
    }
}

struct TcpPortsInner {
    map: BTreeMap<u16, u64>,
    cursor: u16,
}

struct UdpPortsInner {
    set: BTreeSet<u16>,
    cursor: u16,
}

pub(super) struct PortAllocator {
    tcp_ipv4: Mutex<TcpPortsInner>,
    tcp_ipv6: Mutex<TcpPortsInner>,
    udp_ipv4: Mutex<UdpPortsInner>,
    udp_ipv6: Mutex<UdpPortsInner>,
}

pub(super) static PORT_ALLOC: PortAllocator = PortAllocator::new();

impl PortAllocator {
    pub(super) const fn new() -> Self {
        Self {
            tcp_ipv4: Mutex::new(TcpPortsInner {
                map: BTreeMap::new(),
                cursor: u16::MAX >> 2,
            }),
            tcp_ipv6: Mutex::new(TcpPortsInner {
                map: BTreeMap::new(),
                cursor: u16::MAX >> 2,
            }),
            udp_ipv4: Mutex::new(UdpPortsInner {
                set: BTreeSet::new(),
                cursor: u16::MAX >> 2,
            }),
            udp_ipv6: Mutex::new(UdpPortsInner {
                set: BTreeSet::new(),
                cursor: u16::MAX >> 2,
            }),
        }
    }

    /// Allocate an ephemeral TCP IPv4 port.
    pub(super) fn get_ephemeral_tcp_ipv4(&self) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        for _ in 0..(u16::MAX >> 2) {
            ports.cursor = ports.cursor.wrapping_add(1);
            let port = if ports.cursor == 0 {
                u16::MAX >> 2
            } else {
                ports.cursor
            };
            if let Entry::Vacant(e) = ports.map.entry(port) {
                e.insert(1);
                return Some(TcpPort::new(port, true));
            }
        }
        None
    }

    /// Claim a specific TCP IPv4 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_tcp_ipv4(&self, port: u16) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        if let Entry::Vacant(e) = ports.map.entry(port) {
            e.insert(1);
            Some(TcpPort::new(port, true))
        } else {
            None
        }
    }

    /// Increment the reference count for a TCP IPv4 port (used by `TcpListener::accept`).
    pub(super) fn increment_ref_tcp_ipv4(&self, port: u16) -> TcpPort {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        if let Some(e) = ports.map.get_mut(&port) {
            *e += 1;
        } else {
            ports.map.insert(port, 1);
        }
        TcpPort::new(port, true)
    }

    /// Decrement the reference count for a TCP IPv4 port, freeing it when it reaches zero.
    pub(super) fn decrement_ref_tcp_ipv4(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        if let Some(e) = ports.map.get_mut(&port) {
            *e -= 1;
            if *e == 0 {
                ports.map.remove(&port);
            }
        }
    }

    /// Allocate an ephemeral TCP IPv6 port.
    pub(super) fn get_ephemeral_tcp_ipv6(&self) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        for _ in 0..(u16::MAX >> 2) {
            ports.cursor = ports.cursor.wrapping_add(1);
            let port = if ports.cursor == 0 {
                u16::MAX >> 2
            } else {
                ports.cursor
            };
            if let Entry::Vacant(e) = ports.map.entry(port) {
                e.insert(1);
                return Some(TcpPort::new(port, false));
            }
        }
        None
    }

    /// Claim a specific TCP IPv6 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_tcp_ipv6(&self, port: u16) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        if let Entry::Vacant(e) = ports.map.entry(port) {
            e.insert(1);
            Some(TcpPort::new(port, false))
        } else {
            None
        }
    }

    /// Increment the reference count for a TCP IPv6 port.
    pub(super) fn increment_ref_tcp_ipv6(&self, port: u16) -> TcpPort {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        if let Some(e) = ports.map.get_mut(&port) {
            *e += 1;
        } else {
            ports.map.insert(port, 1);
        }
        TcpPort::new(port, false)
    }

    /// Decrement the reference count for a TCP IPv6 port, freeing it when it reaches zero.
    pub(super) fn decrement_ref_tcp_ipv6(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        if let Some(e) = ports.map.get_mut(&port) {
            *e -= 1;
            if *e == 0 {
                ports.map.remove(&port);
            }
        }
    }

    /// Allocate an ephemeral UDP IPv4 port.
    pub(super) fn get_ephemeral_udp_ipv4(&self) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv4.lock(&mut node);
        for _ in 0..(u16::MAX >> 2) {
            ports.cursor = ports.cursor.wrapping_add(1);
            let port = if ports.cursor == 0 {
                u16::MAX >> 2
            } else {
                ports.cursor
            };
            if ports.set.insert(port) {
                return Some(UdpPort {
                    port,
                    is_ipv4: true,
                });
            }
        }
        None
    }

    /// Claim a specific UDP IPv4 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_udp_ipv4(&self, port: u16) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv4.lock(&mut node);
        if ports.set.insert(port) {
            Some(UdpPort {
                port,
                is_ipv4: true,
            })
        } else {
            None
        }
    }

    /// Free a UDP IPv4 port.
    pub(super) fn free_udp_ipv4(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv4.lock(&mut node);
        ports.set.remove(&port);
    }

    /// Allocate an ephemeral UDP IPv6 port.
    pub(super) fn get_ephemeral_udp_ipv6(&self) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv6.lock(&mut node);
        for _ in 0..(u16::MAX >> 2) {
            ports.cursor = ports.cursor.wrapping_add(1);
            let port = if ports.cursor == 0 {
                u16::MAX >> 2
            } else {
                ports.cursor
            };
            if ports.set.insert(port) {
                return Some(UdpPort {
                    port,
                    is_ipv4: false,
                });
            }
        }
        None
    }

    /// Claim a specific UDP IPv6 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_udp_ipv6(&self, port: u16) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv6.lock(&mut node);
        if ports.set.insert(port) {
            Some(UdpPort {
                port,
                is_ipv4: false,
            })
        } else {
            None
        }
    }

    /// Free a UDP IPv6 port.
    pub(super) fn free_udp_ipv6(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv6.lock(&mut node);
        ports.set.remove(&port);
    }
}
