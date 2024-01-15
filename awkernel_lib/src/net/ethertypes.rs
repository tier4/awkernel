#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum EtherTypes {
    Ieee8023 = 0x0004, // IEEE 802.3 Ethernet frame
    IPv4 = 0x0800,     // IPv4
    Arp = 0x0806,      // ARP
    Vlan = 0x8100,     // VLAN-tagged frame (IEEE 802.1Q) and Shortest Path Bridging IEEE 802.1aq[8]
    IPv6 = 0x86DD,     // IPv6
}
