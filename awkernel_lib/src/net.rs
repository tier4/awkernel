use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{collections::BTreeMap, format, string::String, sync::Arc, vec, vec::Vec};
use core::{fmt::Display, net::Ipv4Addr};
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    time::Instant,
    wire::{EthernetAddress, HardwareAddress, IpAddress, IpCidr, Ipv4Address},
};

use self::{
    if_net::{IfNet, NetDriver, NetDriverRef},
    net_device::NetDevice,
};

pub mod ether;
pub mod ethertypes;
mod if_net;
pub mod ip;
pub mod ipv6;
pub mod multicast;
pub mod net_device;
pub mod tcp;
pub mod udp;

#[derive(Debug)]
pub enum NetManagerError {
    InvalidInterfaceID,
}

#[derive(Debug)]
pub struct IfStatus {
    pub interface_id: u64,
    pub device_name: &'static str,
    pub ipv4_addrs: Vec<(Ipv4Addr, u8)>,
    pub ipv4_gateway: Option<Ipv4Addr>,
    pub link_up: bool,
    pub link_speed_mbs: u64,
    pub full_duplex: bool,
    pub mac_address: [u8; 6],
}

impl Display for IfStatus {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        let mut ipv4_addr = String::new();
        for (addr, plen) in self.ipv4_addrs.iter() {
            ipv4_addr.push_str(&format!("{}/{}\r\n", addr, plen));
        }

        let ipv4_gateway = match self.ipv4_gateway {
            Some(addr) => format!("{}", addr),
            None => String::from("None"),
        };

        write!(
            f,
            "[{}] {}:\r\n    IPv4 address: {}\r\n    IPv4 gateway: {}\r\n    MAC address: {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}\r\n    Link up: {}, Link speed: {} Mbps, Full duplex: {}",
            self.interface_id,
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
    interfaces: BTreeMap<u64, Arc<IfNet>>,
    interface_id: u64,
}

pub fn get_interfaces() -> Vec<IfStatus> {
    vec![]
}

pub fn add_interface(inner: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) {
    // TODO
}

pub fn if_net_interrupt(irq: u16) {
    // TODO
}

// pub struct NetManager {
//     interfaces: Vec<Arc<IfNet>>,
//     irq_to_interfaces: BTreeMap<u16, Arc<IfNet>>,
// }

// impl NetManager {
//     const fn new() -> Self {
//         Self {
//             interfaces: Vec::new(),
//             irq_to_interfaces: BTreeMap::new(),
//         }
//     }

//     // pub fn add_interface(&mut self, inner: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) {
//     //     let hardware_addr = HardwareAddress::Ethernet(EthernetAddress(inner.mac_address()));
//     //     let config = Config::new(hardware_addr);
//     //     let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
//     //     let driver = NetDriver {
//     //         inner,
//     //         vlan,
//     //         que_id: 0,
//     //     };
//     //     let mut device_ref = NetDriverRef {
//     //         ref_net_driver: &driver,
//     //     };

//     //     let interface = Mutex::new(Interface::new(config, &mut device_ref, timestamp));

//     //     let value = Arc::new(IfNet {
//     //         driver,
//     //         interface,
//     //         ipv4_gateway: Mutex::new(None),
//     //         socket_set: Mutex::new(SocketSet::new(vec![])),
//     //     });

//     //     for irq in value.driver.inner.irqs() {
//     //         self.irq_to_interfaces.insert(irq, value.clone());
//     //     }

//     //     self.interfaces.push(value);
//     // }

//     // pub fn add_ipv4_addr(
//     //     &mut self,
//     //     mac: &[u8; 6],
//     //     addr: Ipv4Addr,
//     //     plen: u8,
//     // ) -> Result<(), NetManagerError> {
//     //     let netif = self
//     //         .interfaces
//     //         .iter_mut()
//     //         .find(|d| d.driver.inner.mac_address() == *mac)
//     //         .ok_or(NetManagerError::InvalidInterfaceID)?;

//     //     let mut node = MCSNode::new();
//     //     let mut interface = netif.interface.lock(&mut node);
//     //     interface.update_ip_addrs(|ip_addrs| {
//     //         let octets = addr.octets();

//     //         ip_addrs
//     //             .push(IpCidr::new(
//     //                 IpAddress::v4(octets[0], octets[1], octets[2], octets[3]),
//     //                 plen,
//     //             ))
//     //             .unwrap();
//     //     });

//     //     Ok(())
//     // }

//     pub fn set_ipv4_gateway(
//         &mut self,
//         mac: &[u8; 6],
//         addr: Ipv4Addr,
//     ) -> Result<(), NetManagerError> {
//         let netif = self
//             .interfaces
//             .iter_mut()
//             .find(|d| d.driver.inner.mac_address() == *mac)
//             .ok_or(NetManagerError::InvalidInterfaceID)?;

//         let octets = addr.octets();
//         {
//             let mut node = MCSNode::new();
//             let mut interface = netif.interface.lock(&mut node);

//             if interface
//                 .routes_mut()
//                 .add_default_ipv4_route(Ipv4Address::new(
//                     octets[0], octets[1], octets[2], octets[3],
//                 ))
//                 .is_err()
//             {
//                 log::error!("set default IPv4 route error, MAC = {:x?}", mac);
//             }
//         }

//         let mut node = MCSNode::new();
//         let mut ipv4_gateway = netif.ipv4_gateway.lock(&mut node);
//         *ipv4_gateway = Some(addr);

//         Ok(())
//     }

//     pub fn get_interfaces(&self) -> Vec<IfStatus> {
//         let mut result = Vec::new();

//         for netif in self.interfaces.iter() {
//             let inner = &netif.driver.inner;
//             let mac_address = inner.mac_address();
//             let link_up = inner.link_up();
//             let link_speed_mbs = inner.link_speed();
//             let full_duplex = inner.full_duplex();

//             let mut ipv4_addrs = Vec::new();

//             {
//                 let mut node = MCSNode::new();
//                 let interface = netif.interface.lock(&mut node);
//                 for cidr in interface.ip_addrs().iter() {
//                     if let IpAddress::Ipv4(addr) = cidr.address() {
//                         let addr = Ipv4Addr::new(addr.0[0], addr.0[1], addr.0[2], addr.0[3]);
//                         ipv4_addrs.push((addr, cidr.prefix_len()));
//                     }
//                 }
//             }

//             let mut node = MCSNode::new();
//             let ipv4_gateway = *netif.ipv4_gateway.lock(&mut node);

//             let device_name = inner.device_short_name();

//             result.push(IfStatus {
//                 device_name,
//                 ipv4_addrs,
//                 ipv4_gateway,
//                 link_up,
//                 link_speed_mbs,
//                 full_duplex,
//                 mac_address,
//             });
//         }

//         result
//     }
// }

// pub static NET_MANAGER: RwLock<NetManager> = RwLock::new(NetManager::new());
// pub static IRQS: Mutex<Vec<u16>> = Mutex::new(Vec::new());
// pub static WAKER: Mutex<Option<core::task::Waker>> = Mutex::new(None);

// pub fn get_interfaces() -> Vec<IfStatus> {
//     let net_manager = NET_MANAGER.read();
//     net_manager.get_interfaces()
// }

// /// Service routine for network device interrupt.
// /// This routine should be called by interrupt handlers provided by device drivers.
// pub fn netif_interrupt(irq: u16) {
//     {
//         let mut node = MCSNode::new();
//         let mut irqs = IRQS.lock(&mut node);
//         irqs.push(irq);
//     }

//     let mut node = MCSNode::new();
//     let mut waker = WAKER.lock(&mut node);
//     if let Some(waker) = waker.take() {
//         waker.wake();
//     }
// }

// /// Register a waker for a network device interrupt service.
// ///
// /// The old waker will be replaced.
// /// The waker will be called when the network device interrupt occurs once
// /// and it will be removed after it is called.
// pub fn register_network_interrupt_service_waker(waker: core::task::Waker) {
//     let mut node = MCSNode::new();
//     let mut w = WAKER.lock(&mut node);
//     *w = Some(waker);
// }

// pub fn has_pending_irqs() -> bool {
//     let mut node = MCSNode::new();
//     let irqs = IRQS.lock(&mut node);
//     !irqs.is_empty()
// }

// /// Handle network device interrupt actually.
// pub fn network_interrupt_service() {
//     let irqs = {
//         let mut node = MCSNode::new();
//         let mut irqs = IRQS.lock(&mut node);
//         let mut new_irqs = Vec::new();
//         core::mem::swap(irqs.as_mut(), &mut new_irqs);
//         new_irqs
//     };

//     let net_manager = NET_MANAGER.read();

//     {
//         for irq in irqs.iter() {
//             if let Some(interface) = net_manager.irq_to_interfaces.get(irq) {
//                 if let Err(e) = interface.driver.inner.interrupt(*irq) {
//                     log::error!(
//                         "{}: netif interrupt error, {:?}",
//                         interface.driver.inner.device_short_name(),
//                         e
//                     );
//                 } else {
//                     let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
//                     let mut device_ref = NetDriverRef {
//                         ref_net_driver: &interface.driver,
//                     };

//                     let mut node = MCSNode::new();
//                     let mut iface = interface.interface.lock(&mut node);

//                     let mut node = MCSNode::new();
//                     let mut socket_set = interface.socket_set.lock(&mut node);

//                     iface.poll(timestamp, &mut device_ref, &mut socket_set);
//                 }
//             }
//         }
//     }
// }
