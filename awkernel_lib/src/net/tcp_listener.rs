use super::{ip_addr::IpAddr, tcp_stream::SockTcpStream, NetManagerError};

#[cfg(not(feature = "std"))]
mod tcp_listener_no_std;

#[cfg(not(feature = "std"))]
pub use tcp_listener_no_std::TcpListener;

#[cfg(feature = "std")]
mod tcp_listener_std;

#[cfg(feature = "std")]
pub use tcp_listener_std::TcpListener;

pub trait SockTcpListener<T>
where
    Self: Sized,
    T: SockTcpStream,
{
    fn bind_on_interface(
        interface_id: u64,
        addr: &IpAddr,
        port: Option<u16>,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
        backlogs: usize,
    ) -> Result<Self, NetManagerError>;

    fn accept(&mut self, waker: &core::task::Waker) -> Result<Option<T>, NetManagerError>;
}
