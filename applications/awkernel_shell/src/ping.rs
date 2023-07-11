use alloc::collections::BTreeMap;
use awkernel_lib::{console, delay::uptime, net::NETMASTER, sync::mutex::MCSNode};
use byteorder::{ByteOrder, NetworkEndian};
use smoltcp::{
    iface::SocketSet,
    phy::Device,
    socket::icmp,
    time::{Duration, Instant},
    wire::{Icmpv4Packet, Icmpv4Repr, Icmpv6Packet, Icmpv6Repr, IpAddress, IpCidr, Ipv4Address},
};

macro_rules! send_icmp_ping {
    ( $repr_type:ident, $packet_type:ident, $ident:expr, $seq_no:expr,
      $echo_payload:expr, $socket:expr, $remote_addr:expr ) => {{
        let icmp_repr = $repr_type::EchoRequest {
            ident: $ident,
            seq_no: $seq_no,
            data: &$echo_payload,
        };

        let icmp_payload = $socket.send(icmp_repr.buffer_len(), $remote_addr).unwrap();

        let icmp_packet = $packet_type::new_unchecked(icmp_payload);
        (icmp_repr, icmp_packet)
    }};
}

macro_rules! get_icmp_pong {
    ( $repr_type:ident, $repr:expr, $payload:expr, $waiting_queue:expr, $remote_addr:expr,
      $timestamp:expr, $received:expr ) => {{
        if let $repr_type::EchoReply { seq_no, data, .. } = $repr {
            if let Some(_) = $waiting_queue.get(&seq_no) {
                let packet_timestamp_ms = NetworkEndian::read_i64(data);
                console::print(&format!(
                    "{} bytes from {}: icmp_seq={}, time={}ms",
                    data.len(),
                    $remote_addr,
                    seq_no,
                    $timestamp.total_millis() - packet_timestamp_ms
                ));
                $waiting_queue.remove(&seq_no);
                $received += 1;
            }
        }
    }};
}

pub(crate) fn icmp_test() {
    let remote_addr = IpAddress::v4(10, 0, 2, 2);
    let count = 4;
    let interval = Duration::from_secs(1);
    let timeout = Duration::from_secs(5);
    let node = &mut MCSNode::new();
    let mut net_master = NETMASTER.lock(node);
    let (device, mut iface) = net_master.create_iface().unwrap();
    let device_caps = device.capabilities();
    // register the ip address
    iface.update_ip_addrs(|ip_addrs| {
        ip_addrs
            .push(IpCidr::new(IpAddress::v4(10, 0, 2, 15), 24))
            .unwrap();
    });

    // route gateway
    iface
        .routes_mut()
        .add_default_ipv4_route(Ipv4Address::new(10, 0, 2, 2))
        .unwrap();

    let icmp_rx_buffer = icmp::PacketBuffer::new(vec![icmp::PacketMetadata::EMPTY], vec![0; 256]);
    let icmp_tx_buffer = icmp::PacketBuffer::new(vec![icmp::PacketMetadata::EMPTY], vec![0; 256]);
    let icmp_socket = icmp::Socket::new(icmp_rx_buffer, icmp_tx_buffer);
    let mut sockets = SocketSet::new(vec![]);
    let icmp_handle = sockets.add(icmp_socket);
    let mut send_at = Instant::from_millis(0);
    let mut seq_no = 0;
    let mut received = 0;
    let mut echo_payload = [0xffu8; 40];
    let mut waiting_queue = BTreeMap::new();
    let ident = 0x22b;

    loop {
        let timestamp = Instant::from_micros(uptime() as i64);
        iface.poll(timestamp, device, &mut sockets);

        let timestamp = Instant::from_micros(uptime() as i64);
        let socket = sockets.get_mut::<icmp::Socket>(icmp_handle);
        if !socket.is_open() {
            socket.bind(icmp::Endpoint::Ident(ident)).unwrap();
            send_at = timestamp;
        }

        if socket.can_send() && seq_no < count as u16 && send_at <= timestamp {
            NetworkEndian::write_i64(&mut echo_payload, timestamp.total_millis());

            match remote_addr {
                IpAddress::Ipv4(_) => {
                    let (icmp_repr, mut icmp_packet) = send_icmp_ping!(
                        Icmpv4Repr,
                        Icmpv4Packet,
                        ident,
                        seq_no,
                        echo_payload,
                        socket,
                        remote_addr
                    );
                    icmp_repr.emit(&mut icmp_packet, &device_caps.checksum);
                }
                IpAddress::Ipv6(_) => {
                    let (icmp_repr, mut icmp_packet) = send_icmp_ping!(
                        Icmpv6Repr,
                        Icmpv6Packet,
                        ident,
                        seq_no,
                        echo_payload,
                        socket,
                        remote_addr
                    );
                    icmp_repr.emit(
                        &iface.ipv6_addr().unwrap().into_address(),
                        &remote_addr,
                        &mut icmp_packet,
                        &device_caps.checksum,
                    );
                }
            }

            waiting_queue.insert(seq_no, timestamp);
            seq_no += 1;
            send_at += interval;
        }

        if socket.can_recv() {
            let (payload, _) = socket.recv().unwrap();

            match remote_addr {
                IpAddress::Ipv4(_) => {
                    let icmp_packet = Icmpv4Packet::new_checked(&payload).unwrap();
                    let icmp_repr = Icmpv4Repr::parse(&icmp_packet, &device_caps.checksum).unwrap();
                    get_icmp_pong!(
                        Icmpv4Repr,
                        icmp_repr,
                        payload,
                        waiting_queue,
                        remote_addr,
                        timestamp,
                        received
                    );
                }
                IpAddress::Ipv6(_) => {
                    let icmp_packet = Icmpv6Packet::new_checked(&payload).unwrap();
                    let icmp_repr = Icmpv6Repr::parse(
                        &remote_addr,
                        &iface.ipv6_addr().unwrap().into_address(),
                        &icmp_packet,
                        &device_caps.checksum,
                    )
                    .unwrap();
                    get_icmp_pong!(
                        Icmpv6Repr,
                        icmp_repr,
                        payload,
                        waiting_queue,
                        remote_addr,
                        timestamp,
                        received
                    );
                }
            }
        }

        waiting_queue.retain(|seq, from| {
            if timestamp - *from < timeout {
                true
            } else {
                console::print(&format!("From {remote_addr} icmp_seq={seq} timeout"));
                false
            }
        });

        if seq_no == count as u16 && waiting_queue.is_empty() {
            break;
        }
    }

    console::print(&format!("--- {remote_addr} ping statistics ---"));
    console::print(&format!(
        "{} packets transmitted, {} received, {:.0}% packet loss",
        seq_no,
        received,
        100.0 * (seq_no - received) as f64 / seq_no as f64
    ));
}
