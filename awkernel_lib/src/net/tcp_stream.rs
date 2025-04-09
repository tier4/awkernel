use alloc::sync::Arc;

use crate::sync::{mcs::MCSNode, mutex::Mutex};

use super::{ip_addr::IpAddr, NetManagerError};

#[cfg(not(feature = "std"))]
mod tcp_stream_no_std;

#[cfg(not(feature = "std"))]
pub use tcp_stream_no_std::TcpStream;

#[cfg(feature = "std")]
mod tcp_stream_std;

#[cfg(feature = "std")]
pub use tcp_stream_std::TcpStream;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpResult {
    Ok(usize),
    WouldBlock,
    CloseLocal,
    CloseRemote,
    Unreachable,
    InvalidState,
}

/// Close all connections that are in the closed state.
/// This function should be called periodically to clean up closed connections.
#[inline(always)]
pub fn close_connections() {
    #[cfg(not(feature = "std"))]
    tcp_stream_no_std::close_connections();
}

pub struct TcpStreamTx<T: SockTcpStream + Send> {
    stream: Arc<Mutex<T>>,
}

impl<T: SockTcpStream + Send> TcpStreamTx<T> {
    pub fn send(&mut self, buf: &[u8], waker: &core::task::Waker) -> TcpResult {
        let mut node = MCSNode::new();
        let mut stream = self.stream.lock(&mut node);
        stream.send(buf, waker)
    }
}

pub struct TcpStreamRx<T: SockTcpStream + Send> {
    stream: Arc<Mutex<T>>,
}

impl<T: SockTcpStream + Send> TcpStreamRx<T> {
    pub fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult {
        let mut node = MCSNode::new();
        let mut stream = self.stream.lock(&mut node);
        stream.recv(buf, waker)
    }
}

pub trait SockTcpStream
where
    Self: Sized + Send,
{
    fn connect(
        interface_id: u64,
        remote_addr: IpAddr,
        remote_port: u16,
        local_port: Option<u16>,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
    ) -> Result<Self, NetManagerError>;

    fn send(&mut self, buf: &[u8], waker: &core::task::Waker) -> TcpResult;
    fn recv(&mut self, buf: &mut [u8], waker: &core::task::Waker) -> TcpResult;
    fn split(self) -> (TcpStreamTx<Self>, TcpStreamRx<Self>);
    fn remote_addr(&self) -> Result<(IpAddr, u16), NetManagerError>;
}
