use crate::pcie::capability::virtio::VirtioCap;
use crate::pcie::BaseAddress;
use crate::pcie::PCIeInfo;

// The network device has the following device configuration layout.
// All of the device configuration fields are read-only for the driver.
// struct virtio_net_config {
//     mac: [u8; 6],
//     status: u16,
//     max_virtqueue_pairs: u16,
//     mtu: u16,
//     speed: u32,
//     duplex: u8,
//     rss_max_key_size: u8,
//     rss_max_indirection_table_length: u16,
//     supported_hash_types: u32,
//     supported_tunnel_types: u32,
// };

const VIRTIO_PCI_NET_CFG_MAC_ADDR_OFFSET: usize = 0x00;

#[derive(Debug)]
pub enum VirtioDriverErr {
    NoBar,
}

#[derive(Debug, Clone)]
pub struct VirtioNetConfig {
    bar: BaseAddress,
    offset: usize,
}

impl VirtioNetConfig {
    pub fn new(info: &PCIeInfo, cap: VirtioCap) -> Self {
        let bar = info
            .get_bar(cap.get_bar() as usize)
            .ok_or(VirtioDriverErr::NoBar)
            .unwrap();

        Self {
            bar,
            offset: cap.get_offset() as usize,
        }
    }

    pub fn virtio_get_mac_addr(&mut self) -> [u8; 6] {
        let mut mac = [0u8; 6];
        for i in 0..6 {
            mac[i] = self
                .bar
                .read8(self.offset + VIRTIO_PCI_NET_CFG_MAC_ADDR_OFFSET + i)
                .unwrap();
        }
        mac
    }
}
