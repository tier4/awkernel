#![cfg(not(feature = "std"))]

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::{
    port_bitmap::{TcpPortSet, UdpPortSet},
    tcp::TcpPort,
};

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

pub(super) struct PortAllocator {
    tcp_ipv4: Mutex<TcpPortSet>,
    tcp_ipv6: Mutex<TcpPortSet>,
    udp_ipv4: Mutex<UdpPortSet>,
    udp_ipv6: Mutex<UdpPortSet>,
}

pub(super) static PORT_ALLOC: PortAllocator = PortAllocator::new();

impl PortAllocator {
    pub(super) const fn new() -> Self {
        Self {
            tcp_ipv4: Mutex::new(TcpPortSet::new()),
            tcp_ipv6: Mutex::new(TcpPortSet::new()),
            udp_ipv4: Mutex::new(UdpPortSet::new()),
            udp_ipv6: Mutex::new(UdpPortSet::new()),
        }
    }

    /// Allocate an ephemeral TCP IPv4 port.
    pub(super) fn get_ephemeral_tcp_ipv4(&self) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        ports.alloc_ephemeral().map(|port| TcpPort::new(port, true))
    }

    /// Claim a specific TCP IPv4 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_tcp_ipv4(&self, port: u16) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        if ports.try_claim(port) {
            Some(TcpPort::new(port, true))
        } else {
            None
        }
    }

    /// Increment the reference count for a TCP IPv4 port (used by `TcpListener::accept`).
    pub(super) fn increment_ref_tcp_ipv4(&self, port: u16) -> TcpPort {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        ports.increment(port);
        TcpPort::new(port, true)
    }

    /// Decrement the reference count for a TCP IPv4 port, freeing it when it reaches zero.
    pub(super) fn decrement_ref_tcp_ipv4(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv4.lock(&mut node);
        ports.decrement(port);
    }

    /// Allocate an ephemeral TCP IPv6 port.
    pub(super) fn get_ephemeral_tcp_ipv6(&self) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        ports
            .alloc_ephemeral()
            .map(|port| TcpPort::new(port, false))
    }

    /// Claim a specific TCP IPv6 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_tcp_ipv6(&self, port: u16) -> Option<TcpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        if ports.try_claim(port) {
            Some(TcpPort::new(port, false))
        } else {
            None
        }
    }

    /// Increment the reference count for a TCP IPv6 port.
    pub(super) fn increment_ref_tcp_ipv6(&self, port: u16) -> TcpPort {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        ports.increment(port);
        TcpPort::new(port, false)
    }

    /// Decrement the reference count for a TCP IPv6 port, freeing it when it reaches zero.
    pub(super) fn decrement_ref_tcp_ipv6(&self, port: u16) {
        let mut node = MCSNode::new();
        let mut ports = self.tcp_ipv6.lock(&mut node);
        ports.decrement(port);
    }

    /// Allocate an ephemeral UDP IPv4 port.
    pub(super) fn get_ephemeral_udp_ipv4(&self) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv4.lock(&mut node);
        ports.alloc_ephemeral().map(|port| UdpPort {
            port,
            is_ipv4: true,
        })
    }

    /// Claim a specific UDP IPv4 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_udp_ipv4(&self, port: u16) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv4.lock(&mut node);
        if ports.try_claim(port) {
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
        ports.free(port);
    }

    /// Allocate an ephemeral UDP IPv6 port.
    pub(super) fn get_ephemeral_udp_ipv6(&self) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv6.lock(&mut node);
        ports.alloc_ephemeral().map(|port| UdpPort {
            port,
            is_ipv4: false,
        })
    }

    /// Claim a specific UDP IPv6 port. Returns `None` if the port is already in use.
    pub(super) fn try_claim_udp_ipv6(&self, port: u16) -> Option<UdpPort> {
        let mut node = MCSNode::new();
        let mut ports = self.udp_ipv6.lock(&mut node);
        if ports.try_claim(port) {
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
        ports.free(port);
    }
}
