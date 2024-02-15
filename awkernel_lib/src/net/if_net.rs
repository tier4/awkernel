use alloc::{collections::BTreeMap, sync::Arc, vec, vec::Vec};
use awkernel_async_lib_verified::ringq::RingQ;
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{self, Checksum, Device, DeviceCapabilities},
    time::Instant,
    wire::HardwareAddress,
};

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::{
    ether::{extract_headers, NetworkHdr, TransportHdr},
    net_device::{EtherFrameBuf, EtherFrameRef, NetCapabilities, NetDevice, PacketHeaderFlags},
};

struct NetDriver {
    inner: Arc<dyn NetDevice + Sync + Send>,
    rx_que_id: usize,

    rx_ringq: Mutex<RingQ<EtherFrameBuf>>,
}

struct NetDriverRef<'a> {
    inner: &'a Arc<dyn NetDevice + Sync + Send>,

    rx_ringq: Option<&'a mut RingQ<EtherFrameBuf>>,
    tx_ringq: &'a mut RingQ<Vec<u8>>,
}

impl<'a> NetDriverRef<'a> {
    fn tx_packet_header_flags(&self, data: &[u8]) -> PacketHeaderFlags {
        let mut flags = PacketHeaderFlags::empty();

        let Ok(ext) = extract_headers(data) else {
            return flags;
        };

        let capabilities = self.capabilities();

        if matches!(ext.network, NetworkHdr::Ipv4(_)) && !capabilities.checksum.ipv4.tx() {
            flags.insert(PacketHeaderFlags::IPV4_CSUM_OUT); // IPv4 checksum offload
        }

        match ext.transport {
            TransportHdr::Tcp(_) => {
                if !capabilities.checksum.tcp.tx() {
                    flags.insert(PacketHeaderFlags::TCP_CSUM_OUT); // TCP checksum offload
                }
            }
            TransportHdr::Udp(_) => {
                if !capabilities.checksum.udp.tx() {
                    flags.insert(PacketHeaderFlags::UDP_CSUM_OUT); // UDP checksum offload
                }
            }
            _ => {}
        }

        flags
    }
}

impl<'a> Device for NetDriverRef<'a> {
    type RxToken<'b> = NRxToken where Self : 'b;
    type TxToken<'b> = NTxToken<'b> where Self: 'b;
    fn capabilities(&self) -> phy::DeviceCapabilities {
        let mut cap = DeviceCapabilities::default();
        cap.max_transmission_unit = 1500;
        cap.max_burst_size = Some(64);

        let capabilities = self.inner.capabilities();

        if capabilities.contains(NetCapabilities::CSUM_IPv4) {
            cap.checksum.ipv4 = Checksum::Rx;
        }

        // TCP and UDP checksum offload is currently not supported
        // because of bugs in the current implementation.

        // if capabilities.contains(NetCapabilities::CSUM_TCPv4 | NetCapabilities::CSUM_TCPv6) {
        //     cap.checksum.tcp = Checksum::Rx;
        // }

        // if capabilities.contains(NetCapabilities::CSUM_UDPv4 | NetCapabilities::CSUM_UDPv6) {
        //     cap.checksum.udp = Checksum::Rx;
        // }

        cap
    }

    /// The additional transmit token makes it possible to generate a reply packet
    /// based on the contents of the received packet, without heap allocation.
    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        if let Some(que) = self.rx_ringq.as_mut() {
            if let Some(data) = que.pop() {
                return Some((
                    NRxToken { data },
                    NTxToken {
                        tx_ring: self.tx_ringq,
                    },
                ));
            }
        }

        None
    }

    /// The real packet transmission is performed when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        if !self.inner.can_send() {
            return None;
        }

        if self.tx_ringq.is_full() {
            return None;
        }

        Some(NTxToken {
            tx_ring: self.tx_ringq,
        })
    }
}

pub(super) struct IfNet {
    vlan: Option<u16>,
    pub(super) inner: Mutex<IfNetInner>,
    rx_irq_to_drvier: BTreeMap<u16, NetDriver>,
    tx_only_ringq: Vec<Mutex<RingQ<Vec<u8>>>>,
    pub(super) net_device: Arc<dyn NetDevice + Sync + Send>,
    pub(super) is_poll_mode: bool,
    poll_driver: Option<NetDriver>,
}

pub(super) struct IfNetInner {
    pub(super) interface: Interface,
    pub(super) socket_set: SocketSet<'static>,
    pub(super) default_gateway_ipv4: Option<smoltcp::wire::Ipv4Address>,
}

impl IfNetInner {
    #[inline(always)]
    pub fn split(&mut self) -> (&mut Interface, &mut SocketSet<'static>) {
        (&mut self.interface, &mut self.socket_set)
    }

    #[inline(always)]
    pub fn get_default_gateway_ipv4(&self) -> Option<smoltcp::wire::Ipv4Address> {
        self.default_gateway_ipv4
    }

    #[inline(always)]
    pub fn set_default_gateway_ipv4(&mut self, gateway: smoltcp::wire::Ipv4Address) {
        if self.default_gateway_ipv4.is_some() {
            self.interface.routes_mut().remove_default_ipv4_route();
        }

        self.default_gateway_ipv4 = Some(gateway);
    }
}

impl IfNet {
    pub fn new(net_device: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) -> Self {
        let interface = {
            let mut tx_ringq = RingQ::new(0);
            let mut net_driver_ref = NetDriverRef {
                inner: &net_device,
                rx_ringq: None,
                tx_ringq: &mut tx_ringq,
            };

            let instant = Instant::from_micros(crate::delay::uptime() as i64);
            let hardware_address =
                HardwareAddress::Ethernet(smoltcp::wire::EthernetAddress(net_device.mac_address()));
            let mut config = Config::new(hardware_address);
            config.random_seed = crate::delay::uptime();

            Interface::new(config, &mut net_driver_ref, instant)
        };

        // Create NetDrivers.
        let mut rx_irq_to_drvier = BTreeMap::new();
        let mut tx_only_ringq = Vec::new();

        for irq in net_device.irqs().into_iter() {
            let rx_ringq = RingQ::new(512);

            if let Some(que_id) = net_device.rx_irq_to_que_id(irq) {
                rx_irq_to_drvier.insert(
                    irq,
                    NetDriver {
                        inner: net_device.clone(),
                        rx_que_id: que_id,
                        rx_ringq: Mutex::new(rx_ringq),
                    },
                );
            }

            let tx_ringq = Mutex::new(RingQ::new(512));
            tx_only_ringq.push(tx_ringq);
        }

        let poll_driver = if net_device.poll_mode() {
            let tx_ringq = Mutex::new(RingQ::new(512));
            tx_only_ringq.push(tx_ringq);

            Some(NetDriver {
                inner: net_device.clone(),
                rx_que_id: 0,
                rx_ringq: Mutex::new(RingQ::new(512)),
            })
        } else {
            None
        };

        // Create a SocketSet.
        let socket_set = SocketSet::new(vec![]);

        let is_poll_mode = net_device.poll_mode();

        IfNet {
            vlan,
            inner: Mutex::new(IfNetInner {
                interface,
                socket_set,
                default_gateway_ipv4: None,
            }),
            rx_irq_to_drvier,
            net_device,
            tx_only_ringq,
            is_poll_mode,
            poll_driver,
        }
    }

    pub fn poll_tx_only(&self, que_id: usize) -> bool {
        let Some(tx_ringq) = self.tx_only_ringq.get(que_id) else {
            return false;
        };

        let mut node = MCSNode::new();
        let mut tx_ringq = tx_ringq.lock(&mut node);

        let mut device_ref = NetDriverRef {
            inner: &self.net_device,
            rx_ringq: None,
            tx_ringq: &mut tx_ringq,
        };

        let timestamp = Instant::from_micros(crate::delay::uptime() as i64);

        let result = {
            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            let (interface, socket_set) = inner.split();

            // device_ref.tx_packet_header_flags(),
            interface.poll(timestamp, &mut device_ref, socket_set)
        };

        // send packets from the queue.
        while !device_ref.tx_ringq.is_empty() {
            if let Some(data) = device_ref.tx_ringq.pop() {
                let tx_packet_header_flags = device_ref.tx_packet_header_flags(&data);

                let data = EtherFrameRef {
                    data: &data,
                    vlan: self.vlan,
                    csum_flags: tx_packet_header_flags,
                };

                if self.net_device.send(data, que_id).is_err() {
                    log::error!("Failed to send a packet.");
                }
            } else {
                break;
            }
        }

        result
    }

    fn poll_rx(&self, ref_net_driver: &NetDriver) -> bool {
        let que_id = ref_net_driver.rx_que_id;
        let Some(tx_ringq) = self.tx_only_ringq.get(que_id) else {
            return false;
        };

        let mut node = MCSNode::new();
        let mut rx_ringq = ref_net_driver.rx_ringq.lock(&mut node);

        // receive packets from the RX queue.
        while !rx_ringq.is_full() {
            if let Ok(Some(data)) = ref_net_driver.inner.recv(ref_net_driver.rx_que_id) {
                let _ = rx_ringq.push(data);
            } else {
                break;
            }
        }

        let mut node = MCSNode::new();
        let mut tx_ringq = tx_ringq.lock(&mut node);

        let mut device_ref = NetDriverRef {
            inner: &ref_net_driver.inner,
            rx_ringq: Some(&mut rx_ringq),
            tx_ringq: &mut tx_ringq,
        };

        let result = {
            let timestamp = Instant::from_micros(crate::delay::uptime() as i64);

            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            let (interface, socket_set) = inner.split();

            interface.poll(timestamp, &mut device_ref, socket_set)
        };

        // send packets from the queue.
        while !device_ref.tx_ringq.is_empty() {
            if let Some(data) = device_ref.tx_ringq.pop() {
                let tx_packet_header_flags = device_ref.tx_packet_header_flags(&data);

                let data = EtherFrameRef {
                    data: &data,
                    vlan: self.vlan,
                    csum_flags: tx_packet_header_flags,
                };

                let _ = self.net_device.send(data, ref_net_driver.rx_que_id);
            } else {
                break;
            }
        }

        result
    }

    #[inline(always)]
    pub fn poll_rx_poll_mode(&self) -> bool {
        let Some(ref_net_driver) = self.poll_driver.as_ref() else {
            return false;
        };

        self.poll_rx(ref_net_driver)
    }

    /// If some packets are processed, return true.
    /// If poll returns true, the caller should call poll again.
    #[inline(always)]
    pub fn poll_rx_irq(&self, irq: u16) -> bool {
        let Some(ref_net_driver) = self.rx_irq_to_drvier.get(&irq) else {
            return false;
        };

        self.poll_rx(ref_net_driver)
    }
}

pub struct NRxToken {
    data: EtherFrameBuf,
}

impl phy::RxToken for NRxToken {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of `smoltcp`.
    fn consume<R, F>(mut self, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        f(&mut self.data.data)
    }
}

pub struct NTxToken<'a> {
    tx_ring: &'a mut RingQ<Vec<u8>>,
}

impl<'a> phy::TxToken for NTxToken<'a> {
    fn consume<R, F>(self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        let mut buf = Vec::with_capacity(len);

        #[allow(clippy::uninit_vec)]
        unsafe {
            buf.set_len(len);
        };

        let result = f(&mut buf[..len]);

        let _ = self.tx_ring.push(buf);

        result
    }
}
