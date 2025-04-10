use core::net::Ipv4Addr;

use super::IpAddr;
use awkernel_lib::net::{
    tcp_listener::SockTcpListener, tcp_stream::SockTcpStream, NetManagerError,
};
use futures::Future;
use pin_project::pin_project;

/// Configuration for TCP.
///
/// # Example
/// ```
/// use awkernel_async_lib::net::tcp::TcpConfig;
///
/// let mut config = TcpConfig::default();
/// config.port = Some(8080);
/// ```
#[derive(Debug, Clone)]
pub struct TcpConfig {
    pub addr: IpAddr,          // The address to bind.
    pub port: Option<u16>,     // The port to bind. If None, an ephemeral port is used.
    pub rx_buffer_size: usize, // The size of the receive buffer in bytes.
    pub tx_buffer_size: usize, // The size of the transmit buffer in bytes.
    pub backlogs: usize,       // The number of backlogs. This is used only for TcpListener.
}

impl Default for TcpConfig {
    fn default() -> Self {
        TcpConfig {
            addr: IpAddr::new_v4(Ipv4Addr::new(0, 0, 0, 0)),
            port: None,
            rx_buffer_size: 1024 * 64,
            tx_buffer_size: 1024 * 64,
            backlogs: 10,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpSocketError {
    SocketCreationError,
    InvalidInterfaceID,
    PortInUse,
}

pub struct TcpListener {
    listener: awkernel_lib::net::tcp_listener::TcpListener,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpSendError {
    Unreachable,
    CloseLocal,
    InvalidState,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TcpRecvError {
    Unreachable,
    CloseRemote,
    InvalidState,
}

impl TcpListener {
    /// Create a new listener.
    /// The listener is bound to the specified address and port.
    pub fn bind_on_interface(
        interface_id: u64,
        config: &TcpConfig,
    ) -> Result<TcpListener, NetManagerError> {
        let listener = awkernel_lib::net::tcp_listener::TcpListener::bind_on_interface(
            interface_id,
            &config.addr,
            config.port,
            config.rx_buffer_size,
            config.tx_buffer_size,
            config.backlogs,
        )?;

        Ok(TcpListener { listener })
    }

    /// Accept a new connection.
    pub async fn accept(&mut self) -> Result<TcpStream, TcpSocketError> {
        TcpAccepter { listener: self }.await
    }
}

#[pin_project]
struct TcpAccepter<'a> {
    listener: &'a mut TcpListener,
}

impl Future for TcpAccepter<'_> {
    type Output = Result<TcpStream, TcpSocketError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();
        let listener = this.listener;
        let result = listener.listener.accept(cx.waker());
        match result {
            Ok(None) => core::task::Poll::Pending,
            Ok(Some(stream)) => core::task::Poll::Ready(Ok(TcpStream { stream })),
            Err(_e) => core::task::Poll::Ready(Err(TcpSocketError::SocketCreationError)),
        }
    }
}

pub struct TcpStream {
    stream: awkernel_lib::net::tcp_stream::TcpStream,
}

impl TcpStream {
    /// Send data to the stream.
    ///
    /// This function returns the number of bytes sent.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::net::{IpAddr, tcp::TcpStream};
    /// use core::str::FromStr;
    /// async fn recv_example() {
    ///     let addr = core::net::Ipv4Addr::from_str("192.168.1.1").unwrap();
    ///     let addr = IpAddr::new_v4(addr);
    ///     let mut stream = TcpStream::connect(0, addr, 80, &Default::default()).await.unwrap();
    ///
    ///     stream.send(b"Hello, Awkernel!\r\n").await.unwrap();
    /// }
    /// ```
    #[inline(always)]
    pub async fn send(&mut self, buf: &[u8]) -> Result<usize, TcpSendError> {
        TcpSender { stream: self, buf }.await
    }

    /// Receive data from the stream.
    ///
    /// This function returns the number of bytes received.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::net::{IpAddr, tcp::TcpStream};
    /// use core::str::FromStr;
    /// async fn recv_example() {
    ///     let addr = core::net::Ipv4Addr::from_str("192.168.1.1").unwrap();
    ///     let addr = IpAddr::new_v4(addr);
    ///     let mut stream = TcpStream::connect(0, addr, 80, &Default::default()).await.unwrap();
    ///
    ///     let mut buf = [0; 1024];
    ///     stream.recv(&mut buf).await.unwrap();
    /// }
    /// ```
    #[inline(always)]
    pub async fn recv(&mut self, buf: &mut [u8]) -> Result<usize, TcpRecvError> {
        TcpReceiver { stream: self, buf }.await
    }

    /// Get the remote address and port.
    pub fn remote_addr(&self) -> Option<(IpAddr, u16)> {
        self.stream.remote_addr().ok()
    }

    /// Connect to the remote host whose IP address and port number are `addr` and `port` on
    /// `interface_id` interface.
    /// `config.addr`, `config.port`, and `config.backlogs` are ignored.
    ///
    /// On std environments `interface_id` and `config` are ignored.
    ///
    /// # Example
    ///
    /// ```
    /// use awkernel_async_lib::net::{IpAddr, tcp::TcpStream};
    /// use core::str::FromStr;
    /// async fn connect_example() {
    ///     let addr = core::net::Ipv4Addr::from_str("192.168.1.1").unwrap();
    ///     let addr = IpAddr::new_v4(addr);
    ///     let stream = TcpStream::connect(0, addr, 80, &Default::default()).await.unwrap();
    /// }
    /// ```
    #[inline(always)]
    pub async fn connect(
        interface_id: u64,
        addr: IpAddr,
        port: u16,
        config: &TcpConfig,
    ) -> Result<TcpStream, TcpSocketError> {
        TcpConnecter {
            interface_id,
            remote_addr: addr,
            remote_port: port,
            rx_buffer_size: config.rx_buffer_size,
            tx_buffer_size: config.tx_buffer_size,
            stream: None,
        }
        .await
    }
}

#[pin_project]
struct TcpConnecter {
    interface_id: u64,
    remote_addr: IpAddr,
    remote_port: u16,
    rx_buffer_size: usize,
    tx_buffer_size: usize,

    stream: Option<awkernel_lib::net::tcp_stream::TcpStream>,
}

impl Future for TcpConnecter {
    type Output = Result<TcpStream, TcpSocketError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();

        if let Some(stream) = this.stream.take() {
            return core::task::Poll::Ready(Ok(TcpStream { stream }));
        }

        let result = awkernel_lib::net::tcp_stream::TcpStream::connect(
            *this.interface_id,
            this.remote_addr,
            *this.remote_port,
            *this.rx_buffer_size,
            *this.tx_buffer_size,
            cx.waker(),
        );

        match result {
            Ok(stream) => {
                *this.stream = Some(stream);
                core::task::Poll::Pending
            }
            Err(NetManagerError::CannotFindInterface) => {
                core::task::Poll::Ready(Err(TcpSocketError::InvalidInterfaceID))
            }
            Err(NetManagerError::PortInUse) => {
                core::task::Poll::Ready(Err(TcpSocketError::PortInUse))
            }
            Err(_) => core::task::Poll::Ready(Err(TcpSocketError::SocketCreationError)),
        }
    }
}

#[pin_project]
struct TcpSender<'a> {
    stream: &'a mut TcpStream,
    buf: &'a [u8],
}

impl Future for TcpSender<'_> {
    type Output = Result<usize, TcpSendError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream;
        let result = stream.stream.send(this.buf, cx.waker());
        send_result(result)
    }
}

#[pin_project]
struct TcpReceiver<'a> {
    stream: &'a mut TcpStream,
    buf: &'a mut [u8],
}

impl Future for TcpReceiver<'_> {
    type Output = Result<usize, TcpRecvError>;

    fn poll(
        self: core::pin::Pin<&mut Self>,
        cx: &mut core::task::Context<'_>,
    ) -> core::task::Poll<Self::Output> {
        let this = self.project();
        let stream = this.stream;
        let result = stream.stream.recv(this.buf, cx.waker());
        recv_result(result)
    }
}

#[inline(always)]
fn send_result(
    result: awkernel_lib::net::tcp_stream::TcpResult,
) -> core::task::Poll<Result<usize, TcpSendError>> {
    match result {
        awkernel_lib::net::tcp_stream::TcpResult::Ok(len) => core::task::Poll::Ready(Ok(len)),
        awkernel_lib::net::tcp_stream::TcpResult::WouldBlock => core::task::Poll::Pending,
        awkernel_lib::net::tcp_stream::TcpResult::CloseLocal => {
            core::task::Poll::Ready(Err(TcpSendError::CloseLocal))
        }
        awkernel_lib::net::tcp_stream::TcpResult::InvalidState => {
            core::task::Poll::Ready(Err(TcpSendError::InvalidState))
        }
        awkernel_lib::net::tcp_stream::TcpResult::Unreachable => {
            core::task::Poll::Ready(Err(TcpSendError::Unreachable))
        }
        _ => unreachable!(),
    }
}

#[inline(always)]
fn recv_result(
    result: awkernel_lib::net::tcp_stream::TcpResult,
) -> core::task::Poll<Result<usize, TcpRecvError>> {
    match result {
        awkernel_lib::net::tcp_stream::TcpResult::Ok(len) => core::task::Poll::Ready(Ok(len)),
        awkernel_lib::net::tcp_stream::TcpResult::WouldBlock => core::task::Poll::Pending,
        awkernel_lib::net::tcp_stream::TcpResult::CloseRemote => {
            core::task::Poll::Ready(Err(TcpRecvError::CloseRemote))
        }
        awkernel_lib::net::tcp_stream::TcpResult::InvalidState => {
            core::task::Poll::Ready(Err(TcpRecvError::InvalidState))
        }
        awkernel_lib::net::tcp_stream::TcpResult::Unreachable => {
            core::task::Poll::Ready(Err(TcpRecvError::Unreachable))
        }
        _ => unreachable!(),
    }
}
