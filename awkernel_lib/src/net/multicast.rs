use core::net::Ipv4Addr;

use alloc::collections::BTreeSet;

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct MulticastRangeIPv4 {
    pub start: Ipv4Addr,
    pub end: Ipv4Addr,
}

#[derive(Debug, Clone, Copy, PartialEq, PartialOrd, Ord, Eq)]
pub struct MulticastAddrIPv4 {
    pub addr: Ipv4Addr,
}

pub fn ipv4_addr_to_mac_addr(addr: Ipv4Addr) -> [u8; 6] {
    let octets = addr.octets();
    [0x01, 0x00, 0x5e, octets[1] & 0x7f, octets[2], octets[3]]
}

#[derive(Debug)]
pub struct MulticastIPv4 {
    ranges: BTreeSet<MulticastRangeIPv4>,
    addrs: BTreeSet<MulticastAddrIPv4>,
}

impl MulticastIPv4 {
    pub fn new() -> Self {
        Self {
            ranges: BTreeSet::new(),
            addrs: BTreeSet::new(),
        }
    }

    pub fn addrs_len(&self) -> usize {
        self.addrs.len()
    }

    pub fn ranges_len(&self) -> usize {
        self.ranges.len()
    }

    pub fn add_range(&mut self, start: Ipv4Addr, end: Ipv4Addr) -> bool {
        if !(start.is_multicast() && end.is_multicast()) {
            log::warn!("Invalid multicast range: {} - {}", start, end);
            return false;
        }

        self.ranges.insert(MulticastRangeIPv4 { start, end });

        true
    }

    pub fn add_addr(&mut self, addr: Ipv4Addr) -> bool {
        if !addr.is_multicast() {
            log::warn!("Invalid multicast address: {}", addr);
            return false;
        }

        self.addrs.insert(MulticastAddrIPv4 { addr });
        true
    }

    pub fn remove_addr(&mut self, addr: Ipv4Addr) -> bool {
        self.addrs.remove(&MulticastAddrIPv4 { addr })
    }

    pub fn remove_range(&mut self, start: Ipv4Addr, end: Ipv4Addr) -> bool {
        self.ranges.remove(&MulticastRangeIPv4 { start, end })
    }

    pub fn addrs_iter(&self) -> impl Iterator<Item = Ipv4Addr> + '_ {
        self.addrs.iter().map(|addr| addr.addr)
    }

    pub fn ranges_iter(&self) -> impl Iterator<Item = MulticastRangeIPv4> + '_ {
        self.ranges.iter().map(|range| *range)
    }
}
