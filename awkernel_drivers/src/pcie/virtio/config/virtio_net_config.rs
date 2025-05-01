use crate::pcie::{capability::virtio::VirtioCap, virtio::VirtioDriverErr, BaseAddress, PCIeInfo};

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

const VIRTIO_NET_CONFIG_MAC: usize = 0x00;
const VIRTIO_NET_CONFIG_STATUS: usize = 0x06;

pub struct VirtioNetConfig {
    bar: BaseAddress,
    offset: usize,
}

impl Default for VirtioNetConfig {
    fn default() -> Self {
        Self::new()
    }
}

impl VirtioNetConfig {
    pub fn new() -> Self {
        Self {
            bar: BaseAddress::None,
            offset: 0,
        }
    }

    pub fn init(&mut self, info: &PCIeInfo, cap: VirtioCap) -> Result<(), VirtioDriverErr> {
        self.bar = info
            .get_bar(cap.get_bar() as usize)
            .ok_or(VirtioDriverErr::NoBar)?;

        self.offset = cap.get_offset() as usize;

        Ok(())
    }

    pub fn virtio_get_mac_addr(&mut self) -> Result<[u8; 6], VirtioDriverErr> {
        let mut mac = [0u8; 6];
        for (i, byte) in mac.iter_mut().enumerate() {
            *byte = self
                .bar
                .read8(self.offset + VIRTIO_NET_CONFIG_MAC + i)
                .ok_or(VirtioDriverErr::ReadFailure)?;
        }

        Ok(mac)
    }

    pub fn virtio_get_status(&self) -> Result<u16, VirtioDriverErr> {
        let status = self
            .bar
            .read16(self.offset + VIRTIO_NET_CONFIG_STATUS)
            .ok_or(VirtioDriverErr::ReadFailure)?;

        Ok(status)
    }
}
