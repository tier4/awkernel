use crate::sync::mutex::Mutex;
use alloc::sync::Arc;
use alloc::vec;
use alloc::vec::Vec;
use smoltcp::phy;

pub trait NetDevice {
    fn recv(&mut self) -> Option<Vec<u8>>;
    fn send(&mut self, data: &mut [u8]) -> Option<()>;
    fn can_send(&self) -> bool;
}

pub struct NetDriver {
    inner: Arc<dyn NetDevice>,
}

impl phy::Device for NetDriver {
    type RxToken<'a> = NRxToken where Self : 'a;
    type TxToken<'a> = NTxToken where Self: 'a;
    fn capabilities(&self) -> phy::DeviceCapabilities {
        unimplemented!()
    }

    //  The additional transmit token makes it possible to generate a reply packet
    //  based on the contents of the received packet, without heap allocation.
    fn receive(
        &mut self,
        _timestamp: smoltcp::time::Instant,
    ) -> Option<(Self::RxToken<'_>, Self::TxToken<'_>)> {
        let data = Arc::get_mut(&mut self.inner).unwrap().recv()?;
        Some((
            NRxToken { data },
            NTxToken {
                device: self.inner.clone(),
            },
        ))
    }

    //  The real  packet transmission occurrs when the token is consumed.
    fn transmit(&mut self, _timestamp: smoltcp::time::Instant) -> Option<Self::TxToken<'_>> {
        if self.inner.can_send() {
            Some(NTxToken {
                device: self.inner.clone(),
            })
        } else {
            None
        }
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
    fn consume<R, F>(mut self, len: usize, f: F) -> R
    where
        F: FnOnce(&mut [u8]) -> R,
    {
        // allocate a buffer for raw data
        let mut buffer = vec![0; len];
        // construct packet in buffer
        let result = f(&mut buffer[0..len]);
        // send the buffer

        Arc::get_mut(&mut self.device).unwrap().send(&mut buffer);
        result
    }
}

pub struct NTxToken {
    device: Arc<dyn NetDevice>,
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

    pub fn add_driver(&mut self, inner: Arc<dyn NetDevice>) {
        self.drivers.push(NetDriver { inner });
    }
}

unsafe impl Send for NetMaster {}

pub static NETMASTER: Mutex<NetMaster> = Mutex::new(NetMaster::new());
