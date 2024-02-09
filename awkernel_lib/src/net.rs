use crate::sync::{mcs::MCSNode, mutex::Mutex, rwlock::RwLock};
use alloc::{
    borrow::Cow,
    collections::{btree_map::Entry, BTreeMap, BTreeSet},
    format,
    string::String,
    sync::Arc,
    vec,
    vec::Vec,
};
use core::{fmt::Display, net::Ipv4Addr};
use smoltcp::wire::{IpAddress, IpCidr};

use self::{
    if_net::IfNet,
    net_device::{NetCapabilities, NetDevice},
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
pub mod udp_socket;

#[derive(Debug)]
pub enum NetManagerError {
    InvalidInterfaceID,
    InvalidIPv4Address,
    CannotFindInterface,
    PortInUse,
    SendError,
    RecvError,
}

#[derive(Debug)]
pub struct IfStatus {
    pub interface_id: u64,
    pub device_name: Cow<'static, str>,
    pub ipv4_addrs: Vec<(Ipv4Addr, u8)>,
    pub ipv4_gateway: Option<Ipv4Addr>,
    pub link_up: bool,
    pub link_speed_mbs: u64,
    pub full_duplex: bool,
    pub mac_address: [u8; 6],
    pub irqs: Vec<u16>,
    pub rx_irq_to_que_id: BTreeMap<u16, usize>,
    pub capabilities: NetCapabilities,
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
            "[{}] {}:\r\n    IPv4 address: {}\r\n    IPv4 gateway: {}\r\n    MAC address: {:02x}:{:02x}:{:02x}:{:02x}:{:02x}:{:02x}\r\n    Link up: {}, Link speed: {} Mbps, Full duplex: {}\r\n    Capabilities: {}\r\n    IRQs: {:?}",
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
            self.capabilities,
            self.irqs,
        )
    }
}

static NET_MANAGER: RwLock<NetManager> = RwLock::new(NetManager {
    interfaces: BTreeMap::new(),
    interface_id: 0,
    udp_ports_ipv4: BTreeSet::new(),
    udp_port_ipv4_ephemeral: u16::MAX >> 2,
});

static WAKERS: Mutex<BTreeMap<u16, IRQWaker>> = Mutex::new(BTreeMap::new());

pub struct NetManager {
    interfaces: BTreeMap<u64, Arc<IfNet>>,
    interface_id: u64,
    udp_ports_ipv4: BTreeSet<u16>,
    udp_port_ipv4_ephemeral: u16,
}

pub fn get_interface(interface_id: u64) -> Result<IfStatus, NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let if_net = net_manager
        .interfaces
        .get(&interface_id)
        .ok_or(NetManagerError::InvalidInterfaceID)?;

    let inner = &if_net.net_device;

    let mac_address = inner.mac_address();
    let link_up = inner.link_up();
    let link_speed_mbs = inner.link_speed();
    let full_duplex = inner.full_duplex();

    let mut ipv4_addrs = Vec::new();

    {
        let mut node = MCSNode::new();
        let interface = if_net.inner.lock(&mut node);

        for cidr in interface.interface.ip_addrs().iter() {
            if let IpAddress::Ipv4(addr) = cidr.address() {
                let addr = Ipv4Addr::new(addr.0[0], addr.0[1], addr.0[2], addr.0[3]);
                ipv4_addrs.push((addr, cidr.prefix_len()));
            }
        }
    }

    let irqs = inner.irqs();

    let mut rx_irq_to_que_id = BTreeMap::new();
    for irq in irqs.iter() {
        if let Some(que_id) = inner.rx_irq_to_que_id(*irq) {
            rx_irq_to_que_id.insert(*irq, que_id);
        };
    }

    let capabilities = inner.capabilities();

    let if_status = IfStatus {
        interface_id,
        device_name: inner.device_short_name(),
        ipv4_addrs,
        ipv4_gateway: None,
        link_up,
        link_speed_mbs,
        full_duplex,
        mac_address,
        irqs,
        rx_irq_to_que_id,
        capabilities,
    };

    Ok(if_status)
}

pub fn get_all_interface() -> Vec<IfStatus> {
    let net_manager = NET_MANAGER.read();

    let mut result = Vec::new();

    for id in net_manager.interfaces.keys() {
        if let Ok(if_status) = get_interface(*id) {
            result.push(if_status);
        }
    }

    result
}

enum IRQWaker {
    Waker(core::task::Waker),
    Interrupted,
}

pub fn add_interface(inner: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) {
    let mut net_manager = NET_MANAGER.write();

    if net_manager.interface_id == u64::MAX {
        panic!("interface id overflow");
    }

    let id = net_manager.interface_id;
    net_manager.interface_id += 1;

    let if_net = Arc::new(IfNet::new(inner, vlan));

    net_manager.interfaces.insert(id, if_net);
}

pub fn add_ipv4_addr(interface_id: u64, addr: Ipv4Addr, prefix_len: u8) {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return;
    };

    let mut node = MCSNode::new();
    let mut inner = if_net.inner.lock(&mut node);

    let octets = addr.octets();

    inner.interface.update_ip_addrs(|ip_addrs| {
        if let Err(e) = ip_addrs.push(IpCidr::new(
            IpAddress::v4(octets[0], octets[1], octets[2], octets[3]),
            prefix_len,
        )) {
            log::error!("add_ipv4_addr: {}", e);
        }
    });
}

/// Service routine for network device interrupt.
/// This routine should be called by interrupt handlers provided by device drivers.
pub fn net_interrupt(irq: u16) {
    let mut node = MCSNode::new();
    let mut w = WAKERS.lock(&mut node);

    match w.entry(irq) {
        Entry::Occupied(e) => {
            if matches!(e.get(), IRQWaker::Waker(_)) {
                let IRQWaker::Waker(w) = e.remove() else {
                    return;
                };

                w.wake();
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Interrupted);
        }
    }
}

/// Register a waker for a network device interrupt service.
///
/// The old waker will be replaced.
/// The waker will be called when the network device interrupt occurs once
/// and it will be removed after it is called.
///
/// Returns true if the waker is registered successfully.
/// Returns false if the interrupt occurred before.
pub fn register_waker_for_network_interrupt(irq: u16, waker: core::task::Waker) -> bool {
    let mut node = MCSNode::new();
    let mut w = WAKERS.lock(&mut node);

    let entry = w.entry(irq);

    match entry {
        Entry::Occupied(mut e) => {
            if matches!(e.get(), IRQWaker::Interrupted) {
                e.remove();
                false
            } else {
                e.insert(IRQWaker::Waker(waker));
                true
            }
        }
        Entry::Vacant(e) => {
            e.insert(IRQWaker::Waker(waker));
            true
        }
    }
}

/// If some packets are processed, true is returned.
/// If true is returned, the caller should call this function again.
pub fn handle_interrupt(interface_id: u64, irq: u16) -> bool {
    let interface = {
        let net_manager = NET_MANAGER.read();

        let Some(interface) = net_manager.interfaces.get(&interface_id) else {
            return false;
        };

        interface.clone()
    };

    let _ = interface.net_device.interrupt(irq);
    interface.poll_rx_irq(irq)
}

pub fn up(interface_id: u64) -> Result<(), NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let _ = if_net.net_device.up();

    Ok(())
}

pub fn down(interface_id: u64) -> Result<(), NetManagerError> {
    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let _ = if_net.net_device.down();

    Ok(())
}

pub fn udp_test(interface_id: u64) -> Result<(), NetManagerError> {
    use smoltcp::socket::udp;

    add_ipv4_addr(interface_id, Ipv4Addr::new(192, 168, 100, 15), 24);

    let if_status = get_interface(interface_id).unwrap();
    log::debug!("Interface status: {}", if_status);

    let net_manager = NET_MANAGER.read();

    let Some(if_net) = net_manager.interfaces.get(&interface_id) else {
        return Err(NetManagerError::InvalidInterfaceID);
    };

    let udp_rx_buffer = udp::PacketBuffer::new(
        vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
        vec![0; 65535],
    );
    let udp_tx_buffer = udp::PacketBuffer::new(
        vec![udp::PacketMetadata::EMPTY, udp::PacketMetadata::EMPTY],
        vec![0; 65535],
    );
    let udp_socket = udp::Socket::new(udp_rx_buffer, udp_tx_buffer);

    let mut node = MCSNode::new();
    let mut inner = if_net.inner.lock(&mut node);
    let udp_handle = inner.socket_set.add(udp_socket);

    let address = IpAddress::v4(192, 168, 100, 1);
    let port = 26099;

    let socket = inner.socket_set.get_mut::<udp::Socket>(udp_handle);
    socket.bind(20000).unwrap();

    drop(inner);

    let mut t0 = None;

    loop {
        {
            let mut node = MCSNode::new();
            let mut inner = if_net.inner.lock(&mut node);

            let socket = inner.socket_set.get_mut::<udp::Socket>(udp_handle);

            if socket.can_send() {
                t0 = Some(crate::delay::uptime());
                let _ = socket.send_slice(b"HELLO FROM AUTOWARE KERNEL", (address, port));
            }

            if socket.recv().is_ok() {
                if let Some(t0) = t0.take() {
                    let t1 = crate::delay::uptime();
                    log::debug!("UDP RTT: {} [us]", t1 - t0);
                }
            }
        }

        if_net.poll_tx_only(0);

        crate::delay::wait_millisec(100);
    }
}
