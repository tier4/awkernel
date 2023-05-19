use super::{Ether, EtherErr, MBuf};
use crate::net::ring::{RecvRing, SendRing};
use smoltcp::phy;

///! intel e1000e driver
pub struct E1000E {
    // ring buffer for receiving data
    rx_ring: RecvRing,
    // ring buffer for sending data
    tx_ring: SendRing,
}

impl Ether for E1000E {
    // poll for the received packet
    fn poll(&mut self) -> Result<(), EtherErr> {
        loop {}
    }
    // send packet data stored in buffer
    fn send(&mut self, buffer: &mut MBuf) -> Result<(), EtherErr> {
        unimplemented!()
    }

    fn init_hw(&mut self) -> Result<(), EtherErr> {
        // 1.Disable Interrupts

        // 2. Issue Global Reset and perform General Configuration

        // 3. Setup the PHY and the link

        // 4. Initialize all statistical counters

        // 5. Initialize receive

        // 6. Initialize transmit

        // 7. Enable interrupt

        Ok(())
    }
}

pub struct RxToken(MBuf);

pub struct TxToken(MBuf);

/// Adapting a lazy method such that
/// the receiving and sending operations only occur
/// when the tokens are consumed.
/// Thus the `receive` and ` transmit` only create the token.
impl phy::Device<'_> for E1000E {
    type RxToken = RxToken;
    type TxToken = TxToken;
    fn capabilities(&self) -> smoltcp::phy::DeviceCapabilities {
        unimplemented!()
    }

    fn receive(&mut self) -> Option<(Self::RxToken, Self::TxToken)> {
        None
    }

    fn transmit(&mut self) -> Option<Self::TxToken> {
        None
    }
}

impl phy::RxToken for RxToken {
    /// Store packet data into the buffer.
    /// Closure f will map the raw bytes to the form that
    /// could be used in the higher layer of smoltcp.
    fn consume<R, F>(self, timestamp: smoltcp::time::Instant, f: F) -> smoltcp::Result<R>
    where
        F: FnOnce(&mut [u8]) -> smoltcp::Result<R>,
    {
        unimplemented!()
    }
}

impl phy::TxToken for TxToken {
    /// create a buffer of size `len`
    /// Closure f will construct a packet in the buffer.
    /// Real packet data transmissions occur here.
    fn consume<R, F>(
        self,
        timestamp: smoltcp::time::Instant,
        len: usize,
        f: F,
    ) -> smoltcp::Result<R>
    where
        F: FnOnce(&mut [u8]) -> smoltcp::Result<R>,
    {
        // allocate a buffer for raw data

        // construct packet in buffer

        // send the buffer

        unimplemented!()
    }
}

// Interrupt Mask Set/Read Register
pub(crate) const IMS: usize = 0x000D0;
// Interrupt Mask Clear Register
pub(crate) const IMC: usize = 0x000D8;
