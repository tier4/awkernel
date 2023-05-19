use super::mbuf::MBuf;

pub mod e1000e;

#[derive(Debug)]
pub enum EtherErr {
    FailedToSend,
    FailedToAlloc,
    FailedToInitHW,
}

pub trait Ether {
    // send a packet in buffer
    fn send(&mut self, buffer: &mut MBuf) -> Result<(), EtherErr>;

    // receive a packet, and store it into a buffer
    fn poll(&mut self) -> Result<(), EtherErr>;

    // init the NIC hardware
    fn init_hw(&mut self) -> Result<(), EtherErr>;
}
