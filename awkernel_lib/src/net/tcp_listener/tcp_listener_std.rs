use crate::net::{ip_addr::IpAddr, tcp_stream::TcpStream, NetManagerError};

use super::SockTcpListener;

pub struct TcpListener;

impl SockTcpListener<TcpStream> for TcpListener {
    fn bind_on_interface(
        _interface_id: u64,
        _addr: &IpAddr,
        _port: Option<u16>,
        _rx_buffer_size: usize,
        _tx_buffer_size: usize,
        _backlogs: usize,
    ) -> Result<Self, NetManagerError> {
        todo!();
    }

    fn accept(&mut self, _waker: &core::task::Waker) -> Result<Option<TcpStream>, NetManagerError> {
        todo!();
    }
}
