pub struct TcpStream {
    pub(super) handle: smoltcp::iface::SocketHandle,
    pub(super) interface_id: u64,
}
