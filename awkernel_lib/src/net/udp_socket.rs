#[cfg(not(feature = "std"))]
mod udp_socket_no_std;

#[cfg(not(feature = "std"))]
pub use udp_socket_no_std::UdpSocket;

#[cfg(feature = "std")]
mod udp_socket_std;

#[cfg(feature = "std")]
pub use udp_socket_std::UdpSocket;

use crate::net::ip_addr::IpAddr;

use super::NetManagerError;

pub trait SockUdp
where
    Self: Sized,
{
    /// Create a UDP socket for IPv4.
    /// This function is for `awkernel_async_lib`,
    /// and it is not intended to be used directly.
    ///
    /// Not that `interface_id`, `rx_buffer_size`, and `tx_buffer_size` are ignored on std environments.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_lib::net::{ip_addr::IpAddr, udp_socket::{SockUdp, UdpSocket}};
    /// use core::net::Ipv4Addr;
    ///
    /// fn example_udp_socket_ipv4() {
    ///     let buf_size = 64 * 1024;
    ///     let handler = UdpSocket::bind_on_interface(
    ///         0,
    ///         IpAddr::new_v4(Ipv4Addr::new(192, 168, 0, 1)),
    ///         Some(10000),
    ///         buf_size,
    ///         buf_size).unwrap();
    /// }
    /// ```
    fn bind_on_interface(
        interface_id: u64,
        addr: IpAddr,
        port: Option<u16>,
        rx_buffer_size: usize,
        tx_buffer_size: usize,
    ) -> Result<Self, NetManagerError>;

    /// Send a UDP packet to the specified address and port.
    /// If the packet is sent successfully, true is returned.
    /// If the packet is not sent because the socket is not ready, false is returned,
    /// and the waker is registered for the socket.
    fn send_to(
        &mut self,
        buf: &[u8],
        addr: &IpAddr,
        port: u16,
        waker: &core::task::Waker,
    ) -> Result<bool, NetManagerError>;

    /// Receive a UDP packet.
    /// If a packet is received, the data, source address, and source port are returned.
    /// If a packet is not received, an error is returned.
    /// If the socket is not ready to receive, the waker is registered for the socket.
    ///
    /// Return value: `(length of the received data, source address, source port)`
    fn recv(
        &mut self,
        buf: &mut [u8],
        waker: &core::task::Waker,
    ) -> Result<Option<(usize, IpAddr, u16)>, NetManagerError>;
}
