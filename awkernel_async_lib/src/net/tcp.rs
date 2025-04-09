use core::net::Ipv4Addr;

use super::IpAddr;
use awkernel_lib::net::{tcp_stream::SockTcpStream, NetManagerError};
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
        config: TcpConfig,
    ) -> Result<TcpListener, NetManagerError> {
        let listener = awkernel_lib::net::tcp_listener::TcpListener::bind_on_interface(
            interface_id,
            config.addr,
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
    #[inline(always)]
    pub async fn send(&mut self, buf: &[u8]) -> Result<usize, TcpSendError> {
        TcpSender { stream: self, buf }.await
    }

    /// Receive data from the stream.
    ///
    /// This function returns the number of bytes received.
    #[inline(always)]
    pub async fn recv(&mut self, buf: &mut [u8]) -> Result<usize, TcpRecvError> {
        TcpReceiver { stream: self, buf }.await
    }

    /// Get the remote address and port.
    pub fn remote_addr(&self) -> Option<(IpAddr, u16)> {
        self.stream.remote_addr().ok()
    }

    pub fn split(self) -> (TcpStreamTx, TcpStreamRx) {
        let stream = self.stream.split();

        (
            TcpStreamTx { stream: stream.0 },
            TcpStreamRx { stream: stream.1 },
        )
    }

    pub fn connect(
        interface_id: u64,
        addr: IpAddr,
        port: u16,
        config: TcpConfig,
    ) -> Result<TcpStream, TcpSocketError> {
        match awkernel_lib::net::tcp_stream::TcpStream::connect(
            interface_id,
            addr,
            port,
            config.port,
            config.rx_buffer_size,
            config.tx_buffer_size,
        ) {
            Ok(stream) => Ok(TcpStream { stream }),
            Err(NetManagerError::CannotFindInterface) => Err(TcpSocketError::InvalidInterfaceID),
            Err(NetManagerError::PortInUse) => Err(TcpSocketError::PortInUse),
            Err(_) => Err(TcpSocketError::SocketCreationError),
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

pub struct TcpStreamTx {
    stream: awkernel_lib::net::tcp_stream::TcpStreamTx<awkernel_lib::net::tcp_stream::TcpStream>,
}

impl TcpStreamTx {
    /// Send data to the stream.
    ///
    /// This function returns the number of bytes sent.
    #[inline(always)]
    pub async fn send(&mut self, buf: &[u8]) -> Result<usize, TcpSendError> {
        TcpStreamTxSender { stream: self, buf }.await
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

#[pin_project]
struct TcpStreamTxSender<'a> {
    stream: &'a mut TcpStreamTx,
    buf: &'a [u8],
}

impl Future for TcpStreamTxSender<'_> {
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

pub struct TcpStreamRx {
    stream: awkernel_lib::net::tcp_stream::TcpStreamRx<awkernel_lib::net::tcp_stream::TcpStream>,
}

impl TcpStreamRx {
    /// Receive data from the stream.
    ///
    /// This function returns the number of bytes received.
    #[inline(always)]
    pub async fn recv(&mut self, buf: &mut [u8]) -> Result<usize, TcpRecvError> {
        TcpStreamRxReceiver { stream: self, buf }.await
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

#[pin_project]
struct TcpStreamRxReceiver<'a> {
    stream: &'a mut TcpStreamRx,
    buf: &'a mut [u8],
}

impl Future for TcpStreamRxReceiver<'_> {
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
