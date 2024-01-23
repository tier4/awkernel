use alloc::{collections::BTreeMap, sync::Arc, vec, vec::Vec};
use awkernel_async_lib_verified::ringq::RingQ;
use smoltcp::{
    iface::{Config, Interface, SocketSet},
    phy::{self, Checksum, Device, DeviceCapabilities},
    time::Instant,
    wire::HardwareAddress,
};

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::net_device::{
    EtherFrameBuf, EtherFrameRef, NetCapabilities, NetDevice, PacketHeaderFlags,
};

pub(super) struct NetDriver {
    pub inner: Arc<dyn NetDevice + Sync + Send>,
    pub que_id: usize,

    rx_ringq: Mutex<RingQ<EtherFrameBuf>>,
    tx_ringq: Mutex<RingQ<Vec<u8>>>,
}

pub(super) struct NetDriverRef<'a> {
    pub ref_net_driver: &'a NetDriver,

    rx_ringq: &'a mut RingQ<EtherFrameBuf>,
    tx_ringq: &'a mut RingQ<Vec<u8>>,
}

impl<'a> NetDriverRef<'a> {
    fn tx_packet_header_flags(&self) -> PacketHeaderFlags {
        let mut flags = PacketHeaderFlags::empty();

        let capabilities = self.capabilities();

        if capabilities.checksum.ipv4.tx() {
            flags.insert(PacketHeaderFlags::IPV4_CSUM_OUT);
        }

        if capabilities.checksum.tcp.tx() {
            flags.insert(PacketHeaderFlags::TCP_CSUM_OUT);
        }

        if capabilities.checksum.udp.tx() {
            flags.insert(PacketHeaderFlags::UDP_CSUM_OUT);
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

        let capabilities = self.ref_net_driver.inner.capabilities();

        if capabilities.contains(NetCapabilities::CSUM_IPv4) {
            cap.checksum.ipv4 = Checksum::Rx;
        }

        if capabilities.contains(NetCapabilities::CSUM_TCPv4 | NetCapabilities::CSUM_TCPv6) {
            cap.checksum.tcp = Checksum::Rx;
        }

        if capabilities.contains(NetCapabilities::CSUM_UDPv4 | NetCapabilities::CSUM_UDPv6) {
            cap.checksum.udp = Checksum::Rx;
        }

        cap
    }

    /// The additional transmit token makes it possible to generate a reply packet
    /// based on the contents of the received packet, without heap allocation.
    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        let data = self.rx_ringq.pop()?;

        Some((
            NRxToken { data },
            NTxToken {
                tx_ring: self.tx_ringq,
            },
        ))
    }

    /// The real packet transmission is performed when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        if !self.ref_net_driver.inner.can_send() {
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
    pub(super) net_device: Arc<dyn NetDevice + Sync + Send>,
}

pub(super) struct IfNetInner {
    pub(super) interface: Interface,
    socket_set: SocketSet<'static>,
}

impl IfNetInner {
    #[inline(always)]
    fn split(&mut self) -> (&mut Interface, &mut SocketSet<'static>) {
        (&mut self.interface, &mut self.socket_set)
    }
}

impl IfNet {
    pub fn new(net_device: Arc<dyn NetDevice + Sync + Send>, vlan: Option<u16>) -> Self {
        // Create Interface.
        let tx_ringq = RingQ::new(0);
        let rx_ringq = RingQ::new(0);

        // Dummy NetDriver.
        // Interface::new() requires a NetDriver.
        let net_driver = NetDriver {
            inner: net_device.clone(),
            que_id: 0,
            rx_ringq: Mutex::new(rx_ringq),
            tx_ringq: Mutex::new(tx_ringq),
        };

        let interface = {
            let mut node = MCSNode::new();
            let mut rx_ringq = net_driver.rx_ringq.lock(&mut node);
            let mut node = MCSNode::new();
            let mut tx_ringq = net_driver.tx_ringq.lock(&mut node);

            let mut net_driver_ref = NetDriverRef {
                ref_net_driver: &net_driver,
                rx_ringq: &mut rx_ringq,
                tx_ringq: &mut tx_ringq,
            };

            let instant = Instant::from_micros(crate::delay::uptime() as i64);
            let hardware_address =
                HardwareAddress::Ethernet(smoltcp::wire::EthernetAddress(net_device.mac_address()));
            let mut config = Config::new(hardware_address);
            config.random_seed = crate::delay::uptime() as u64;

            Interface::new(config, &mut net_driver_ref, instant)
        };

        // Create NetDrivers.
        let mut rx_irq_to_drvier = BTreeMap::new();

        for irq in net_device.irqs().into_iter() {
            let tx_ringq = RingQ::new(512);
            let rx_ringq = RingQ::new(512);

            let que_id = net_device.rx_irq_to_que_id(irq);

            rx_irq_to_drvier.insert(
                irq,
                NetDriver {
                    inner: net_device.clone(),
                    que_id,
                    rx_ringq: Mutex::new(rx_ringq),
                    tx_ringq: Mutex::new(tx_ringq),
                },
            );
        }

        // Create a SocketSet.
        let socket_set = SocketSet::new(vec![]);

        IfNet {
            vlan,
            inner: Mutex::new(IfNetInner {
                interface,
                socket_set,
            }),
            rx_irq_to_drvier,
            net_device,
        }
    }

    /// If some packets are processed, return true.
    /// If poll returns true, the caller should call poll again.
    pub fn poll(&self, irq: u16) -> bool {
        let Some(ref_net_driver) = self.rx_irq_to_drvier.get(&irq) else {
            return false;
        };

        let mut node = MCSNode::new();
        let mut rx_ringq = ref_net_driver.rx_ringq.lock(&mut node);

        let mut node = MCSNode::new();
        let mut tx_ringq = ref_net_driver.tx_ringq.lock(&mut node);

        // receive packets from the RX queue.
        while !rx_ringq.is_full() {
            if let Ok(Some(data)) = ref_net_driver.inner.recv(ref_net_driver.que_id) {
                let _ = rx_ringq.push(data);
            } else {
                break;
            }
        }

        let (tx_packet_header_flags, result) = {
            let mut device_ref = NetDriverRef {
                ref_net_driver,
                rx_ringq: &mut rx_ringq,
                tx_ringq: &mut tx_ringq,
            };

            let timestamp = Instant::from_micros(crate::delay::uptime() as i64);

            let mut node = MCSNode::new();
            let mut inner = self.inner.lock(&mut node);

            let (interface, socket_set) = inner.split();

            (
                device_ref.tx_packet_header_flags(),
                interface.poll(timestamp, &mut device_ref, socket_set),
            )
        };

        // send packets from the queue.
        while !tx_ringq.is_empty() {
            if let Some(data) = tx_ringq.pop() {
                let data = EtherFrameRef {
                    data: &data,
                    vlan: self.vlan,
                    csum_flags: tx_packet_header_flags,
                };

                let _ = ref_net_driver.inner.send(data, ref_net_driver.que_id);
            } else {
                break;
            }
        }

        result
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
        unsafe {
            buf.set_len(len);
        };

        let result = f(&mut buf[..len]);

        let _ = self.tx_ring.push(buf);

        result
    }
}
