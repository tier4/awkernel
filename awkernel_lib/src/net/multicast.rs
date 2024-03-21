use core::net::Ipv4Addr;

use alloc::collections::BTreeSet;

use super::ether::ETHER_ADDR_LEN;

pub fn ipv4_addr_to_mac_addr(addr: Ipv4Addr) -> [u8; 6] {
    let octets = addr.octets();
    [0x01, 0x00, 0x5e, octets[1] & 0x7f, octets[2], octets[3]]
}

#[derive(Debug, Clone)]
pub struct MulticastAddrs {
    addrs: BTreeSet<[u8; ETHER_ADDR_LEN]>,
}

impl MulticastAddrs {
    pub fn new() -> Self {
        Self {
            addrs: BTreeSet::new(),
        }
    }

    #[inline(always)]
    pub fn add_addr(&mut self, addr: [u8; ETHER_ADDR_LEN]) {
        self.addrs.insert(addr);
    }

    #[inline(always)]
    pub fn len(&self) -> usize {
        self.addrs.len()
    }

    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.addrs.is_empty()
    }

    #[inline(always)]
    pub fn iter(&self) -> impl Iterator<Item = &[u8; ETHER_ADDR_LEN]> {
        self.addrs.iter()
    }
}

impl Default for MulticastAddrs {
    fn default() -> Self {
        Self::new()
    }
}
