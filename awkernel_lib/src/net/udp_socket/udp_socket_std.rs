use crate::net::ip_addr::IpAddr;

use super::NetManagerError;

pub struct UdpSocket {}

impl super::SockUdp for UdpSocket {
    fn bind_on_interface(
        _interface_id: u64,
        _addr: IpAddr,
        _port: Option<u16>,
        _rx_buffer_size: usize,
        _tx_buffer_size: usize,
    ) -> Result<Self, NetManagerError> {
        todo!()
    }

    fn send_to(
        &self,
        _buf: &[u8],
        _addr: &IpAddr,
        _port: u16,
        _waker: &core::task::Waker,
    ) -> Result<bool, NetManagerError> {
        todo!()
    }

    fn recv(
        &self,
        _buf: &mut [u8],
        _waker: &core::task::Waker,
    ) -> Result<Option<(usize, IpAddr, u16)>, NetManagerError> {
        todo!()
    }
}
