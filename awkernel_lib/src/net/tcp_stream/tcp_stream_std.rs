use crate::net::{ip_addr::IpAddr, NetManagerError};

use super::{SockTcpStream, TcpResult, TcpStreamRx, TcpStreamTx};

pub struct TcpStream;

impl SockTcpStream for TcpStream {
    fn send(&mut self, buf: &[u8], waker: &core::task::Waker) -> TcpResult {
        todo!();
    }

    fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult {
        todo!();
    }

    fn connect(
        interface_id: u64,
        remote_addr: &IpAddr,
        remote_port: u16,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
        waker: &core::task::Waker,
    ) -> Result<Self, NetManagerError> {
        todo!();
    }

    fn split(self) -> (TcpStreamTx<Self>, TcpStreamRx<Self>) {
        todo!();
    }

    fn remote_addr(&self) -> Result<(IpAddr, u16), NetManagerError> {
        todo!();
    }
}
