#[derive(Debug)]
pub enum EtherErr {
    FailedToSend,
    FailedToAlloc,
    FailedToInitHW,
}

pub trait Ether {
    // send a packet in buffer
    fn send(&self, buffer: &mut [u8]) -> Result<(), smoltcp::Error>;

    // receive a packet, and store it into a buffer
    fn recv(&self) -> Result<&mut [u8], smoltcp::Error>;

    // init the NIC hardware
    unsafe fn init_hw(&mut self) -> Result<(), EtherErr>;
}
