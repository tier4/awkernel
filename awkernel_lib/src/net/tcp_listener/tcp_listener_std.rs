use crate::net::{ip_addr::IpAddr, tcp_stream::TcpStream, NetManagerError};

use super::SockTcpListener;

pub struct TcpListener;

impl SockTcpListener<TcpStream> for TcpListener {
    fn bind_on_interface(
        interface_id: u64,
        addr: &IpAddr,
        port: Option<u16>,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
        backlogs: usize,
    ) -> Result<Self, NetManagerError> {
        todo!();
    }

    fn accept(&mut self, waker: &core::task::Waker) -> Result<Option<TcpStream>, NetManagerError> {
        todo!();
    }
}
