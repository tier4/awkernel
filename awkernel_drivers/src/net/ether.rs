use alloc::vec::Vec;

#[derive(Debug)]
pub enum EtherErr {
    FailedToSend,
    FailedToAlloc,
    FailedToInitHW,
}

pub trait Ether {
    // send a packet in buffer
    fn send(&mut self, buffer: &mut [u8]) -> Result<(), smoltcp::Error>;

    // check whether ready to be sent
    fn is_ready(&self) -> bool;

    // receive a packet, and store it into a buffer
    fn recv(&mut self) -> Option<Vec<u8>>;

    // init the NIC hardware
    unsafe fn init_hw(&mut self) -> Result<(), EtherErr>;
}
