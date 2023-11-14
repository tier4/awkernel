use core::fmt::Display;

use crate::sync::mcs::MCSNode;
use crate::sync::mutex::Mutex;
use alloc::{boxed::Box, format, string::String, sync::Arc, vec, vec::Vec};
use smoltcp::iface::{Config, Interface};
use smoltcp::phy::{self, DeviceCapabilities};
use smoltcp::time::Instant;
use smoltcp::wire::{EthernetAddress, HardwareAddress, Ipv4Address};

pub trait NetDevice {
    fn recv(&mut self) -> Option<Vec<u8>>;
    fn send(&mut self, data: &mut [u8]) -> Option<()>;
    fn can_send(&self) -> bool;
    fn mac_address(&mut self) -> [u8; 6];
    fn link_up(&mut self) -> bool;
    fn full_duplex(&mut self) -> bool;

    // Link speed in Mbps
    fn link_speed(&mut self) -> u64;

    fn device_name(&self) -> &'static str;
}

#[derive(Clone)]
pub struct NetDriver {
    inner: Arc<Mutex<Box<dyn NetDevice + Send>>>,
}

impl phy::Device for NetDriver {
    type RxToken<'a> = NRxToken where Self : 'a;
    type TxToken<'a> = NTxToken where Self: 'a;
    fn capabilities(&self) -> phy::DeviceCapabilities {
        let mut cap = DeviceCapabilities::default();
        cap.max_transmission_unit = 1500;
        cap.max_burst_size = Some(64);
        cap
    }

    //  The additional transmit token makes it possible to generate a reply packet
    //  based on the contents of the received packet, without heap allocation.
    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        let node = &mut MCSNode::new();
        let mut inner = self.inner.lock(node);
        let data = inner.recv()?;
        Some((
            NRxToken { data },
            NTxToken {
                device: self.inner.clone(),
            },
        ))
    }

    //  The real  packet transmission occurrs when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        let node = &mut MCSNode::new();
        let inner = self.inner.lock(node);

        if !inner.can_send() {
            return None;
        }

        Some(NTxToken {
            device: self.inner.clone(),
        })
    }
}

pub struct NRxToken {
    data: Vec<u8>,
}

impl phy::RxToken for NRxToken {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of `smoltcp`.
    fn consume<R, F>(mut self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        f(&mut self.data)
    }
}

impl phy::TxToken for NTxToken {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        // allocate a buffer for raw data
        let mut buffer = vec![0; len];
        // construct packet in buffer
        let result = f(&mut buffer[0..len]);
        // send the buffer
        let node = &mut MCSNode::new();
        let mut inner = self.device.lock(node);
        inner.send(&mut buffer);
        result
    }
}

pub struct NTxToken {
    device: Arc<Mutex<Box<dyn NetDevice + Send>>>,
}

#[derive(Clone)]
pub struct NetIf {
    driver: NetDriver,
    ipv4_addr: Vec<(Ipv4Address, u8)>, // (address, prefix length)
    ipv4_gateway: Option<Ipv4Address>,
}

#[derive(Debug)]
pub enum NetManagerError {
    InvalidInterfaceID,
}

#[derive(Debug)]
pub struct IfStatus {
    pub device_name: &'static str,
    pub ipv4_addr: Vec<(Ipv4Address, u8)>,
    pub ipv4_gateway: Option<Ipv4Address>,
    pub link_up: bool,
    pub link_speed_mbs: u64,
    pub full_duplex: bool,
    pub mac_address: [u8; 6],
}

impl Display for IfStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut ipv4_addr = String::new();
        for (addr, plen) in self.ipv4_addr.iter() {
            ipv4_addr.push_str(&format!("{}/{}\r\n", addr, plen));
        }

        let ipv4_gateway = match self.ipv4_gateway {
            Some(addr) => format!("{}", addr),
            None => String::from("None"),
        };

        write!(
            f,
            "{}:\r\n    IPv4 address: {}\r\n    IPv4 gateway: {}\r\n    MAC address: {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}\r\n    Link up: {}, Link speed: {} Mbps, Full duplex: {}",
            self.device_name,
            ipv4_addr,
            ipv4_gateway,
            self.mac_address[0],
            self.mac_address[1],
            self.mac_address[2],
            self.mac_address[3],
            self.mac_address[4],
            self.mac_address[5],
            self.link_up,
            self.link_speed_mbs,
            self.full_duplex,
        )
    }
}

pub struct NetManager {
    drivers: Vec<NetIf>,
}

impl NetManager {
    const fn new() -> Self {
        Self {
            drivers: Vec::new(),
        }
    }

    pub fn add_interface(&mut self, inner: Arc<Mutex<Box<dyn NetDevice + Send>>>) {
        let value = NetIf {
            driver: NetDriver {
                inner: inner.clone(),
            },
            ipv4_addr: Vec::new(),
            ipv4_gateway: None,
        };

        self.drivers.push(value);
    }

    pub fn add_ipv4_addr(
        &mut self,
        mac: &[u8; 6],
        addr: Ipv4Address,
        plen: u8,
    ) -> Result<(), NetManagerError> {
        let netif = self
            .drivers
            .iter_mut()
            .find(|d| {
                let mut node = MCSNode::new();
                let result = d.driver.inner.lock(&mut node).mac_address() == *mac;
                result
            })
            .ok_or(NetManagerError::InvalidInterfaceID)?;

        netif.ipv4_addr.push((addr, plen));

        Ok(())
    }

    pub fn set_ipv4_gateway(&mut self, mac: &[u8; 6], addr: Ipv4Address) {
        let netif = self
            .drivers
            .iter_mut()
            .find(|d| {
                let mut node = MCSNode::new();
                let result = d.driver.inner.lock(&mut node).mac_address() == *mac;
                result
            })
            .unwrap();

        netif.ipv4_gateway = Some(addr);
    }

    pub fn get_interfaces(&self) -> Vec<IfStatus> {
        let mut result = Vec::new();

        for netif in self.drivers.iter() {
            let mut node = MCSNode::new();
            let mut inner = netif.driver.inner.lock(&mut node);
            let mac_address = inner.mac_address();
            let link_up = inner.link_up();
            let link_speed_mbs = inner.link_speed();
            let full_duplex = inner.full_duplex();

            let ipv4_addr = netif.ipv4_addr.clone();
            let ipv4_gateway = netif.ipv4_gateway;
            let device_name = inner.device_name();

            result.push(IfStatus {
                device_name,
                ipv4_addr,
                ipv4_gateway,
                link_up,
                link_speed_mbs,
                full_duplex,
                mac_address,
            });
        }

        result
    }

    // TODO: fix
    fn create_netif(&mut self) -> Option<(NetDriver, Interface)> {
        if self.drivers.is_empty() {
            return None;
        }

        // TODO: decide how to choose the driver
        let mut device = NetDriver {
            inner: self.drivers[0].driver.inner.clone(),
        };

        let node = &mut MCSNode::new();
        let addr = device.inner.lock(node).mac_address();
        let hardware_addr = HardwareAddress::Ethernet(EthernetAddress(addr));
        let config = Config::new(hardware_addr);
        let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
        let iface = Interface::new(config, &mut device, timestamp);
        Some((device, iface))
    }

    // TODO: fix
    pub fn get_netif() -> Option<(NetDriver, Interface)> {
        let node = &mut MCSNode::new();
        let mut net_manager = NET_MANAGER.lock(node);
        net_manager.create_netif()
    }
}

pub static NET_MANAGER: Mutex<NetManager> = Mutex::new(NetManager::new());

pub fn get_interfaces() -> Vec<IfStatus> {
    let node = &mut MCSNode::new();
    let net_manager = NET_MANAGER.lock(node);
    net_manager.get_interfaces()
}
