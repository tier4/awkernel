use crate::sync::mcs::MCSNode;
use crate::sync::mutex::Mutex;
use alloc::boxed::Box;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use smoltcp::iface::{Config, Interface};
use smoltcp::phy::{self, DeviceCapabilities};
use smoltcp::time::Instant;
use smoltcp::wire::{EthernetAddress, HardwareAddress};

pub trait NetDevice {
    fn recv(&mut self) -> Option<Vec<u8>>;
    fn send(&mut self, data: &mut [u8]) -> Option<()>;
    fn can_send(&self) -> bool;
    fn mac_address(&self) -> [u8; 6];
}

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

        // Arc::_mut(&mut self.device).send(&mut buffer);
        result
    }
}

pub struct NTxToken {
    device: Arc<Mutex<Box<dyn NetDevice + Send>>>,
}

pub struct NetMaster {
    drivers: Vec<NetDriver>,
}

impl NetMaster {
    const fn new() -> Self {
        Self {
            drivers: Vec::new(),
        }
    }

    pub fn add_driver(&mut self, inner: Arc<Mutex<Box<dyn NetDevice + Send>>>) {
        self.drivers.push(NetDriver { inner });
    }

    pub fn create_iface(&mut self) -> Option<(&mut NetDriver, Interface)> {
        if self.drivers.len() == 0 {
            return None;
        }
        let device = &mut self.drivers[0];
        let node = &mut MCSNode::new();
        let addr = device.inner.lock(node).mac_address();
        let hardware_addr = HardwareAddress::Ethernet(EthernetAddress(addr));
        let config = Config::new(hardware_addr);
        let timestamp = Instant::from_micros(crate::delay::uptime() as i64);
        let iface = Interface::new(config, device, timestamp);
        Some((device, iface))
    }
}

unsafe impl Send for NetMaster {}

pub static NETMASTER: Mutex<NetMaster> = Mutex::new(NetMaster::new());
