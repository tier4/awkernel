use alloc::boxed::Box;
use awkernel_async_lib::net::udp::UdpSocket;
use awkernel_lib::ntp::SystemTime;
use core::time::Duration;

const NTP_TIMESTAMP_DELTA: u64 = 2_208_988_800; // seconds between 1900 and 1970

static UNIX_EPOCH: SystemTime = SystemTime::epoch();

/// NTP timestamp in 64-bit fixed-point format. The first 32 bits represent the number of seconds since 1900, and the last 32 bits represent the fraction of a second.
#[derive(Debug, Copy, Clone)]
pub(crate) struct NtpTimestamp(pub u64);

impl NtpTimestamp {
    fn diff(&self, other: &Self) -> Duration {
        let diff = self.0 as i64 - other.0 as i64;
        let secs = diff >> 32;
        let nsecs = ((diff & 0xffffffff) * 1_000_000_000) >> 32;
        Duration::new(secs as u64, nsecs as u32)
    }

    fn from_epoch_us(us: u64) -> Self {
        let secs = us / 1_000_000;
        let nsecs = ((us % 1_000_000) * 1_000) as u32;
        NtpTimestamp((NTP_TIMESTAMP_DELTA + secs) << 32 | nsecs as u64)
    }
}

impl From<NtpTimestamp> for SystemTime {
    fn from(ntp: NtpTimestamp) -> SystemTime {
        let secs = (ntp.0 >> 32).saturating_sub(NTP_TIMESTAMP_DELTA);
        let nsecs = ((ntp.0 & 0xffffffff) * 1_000_000_000) >> 32;
        UNIX_EPOCH + Duration::new(secs, nsecs as u32)
    }
}

impl From<SystemTime> for NtpTimestamp {
    fn from(system: SystemTime) -> NtpTimestamp {
        let dur = system.duration_since(UNIX_EPOCH).unwrap();
        let int = dur.as_secs() + NTP_TIMESTAMP_DELTA;
        let frac = ((dur.subsec_nanos() as u64) << 32) / 1_000_000_000;
        NtpTimestamp(int << 32 | frac)
    }
}

#[derive(Debug)]
pub(crate) struct NtpPacket {
    pub li_vn_mode: u8,
    pub stratum: u8,
    pub poll: i8,
    pub precision: i8,
    pub root_delay: u32,
    pub root_dispersion: u32,
    pub ref_id: u32,
    pub ref_timestamp: NtpTimestamp,
    pub origin_timestamp: NtpTimestamp,
    pub recv_timestamp: NtpTimestamp,
    pub transmit_timestamp: NtpTimestamp,
}

impl NtpPacket {
    pub fn new() -> Self {
        NtpPacket {
            li_vn_mode: 0x1b, // LI = 0, VN = 3, Mode = 3 (client)
            stratum: 0,
            poll: 0,
            precision: 0,
            root_delay: 0,
            root_dispersion: 0,
            ref_id: 0,
            ref_timestamp: NtpTimestamp(0),
            origin_timestamp: NtpTimestamp(0),
            recv_timestamp: NtpTimestamp(0),
            transmit_timestamp: NtpTimestamp(0),
        }
    }

    pub fn to_bytes(self) -> [u8; 48] {
        let mut buffer = [0u8; 48];
        buffer[0] = self.li_vn_mode;
        buffer[1] = self.stratum;
        buffer[2] = self.poll as u8;
        buffer[3] = self.precision as u8;

        buffer[4..8].copy_from_slice(&self.root_delay.to_be_bytes());
        buffer[8..12].copy_from_slice(&self.root_dispersion.to_be_bytes());
        buffer[12..16].copy_from_slice(&self.ref_id.to_be_bytes());
        buffer[16..24].copy_from_slice(&self.ref_timestamp.0.to_be_bytes());
        buffer[24..32].copy_from_slice(&self.origin_timestamp.0.to_be_bytes());
        buffer[32..40].copy_from_slice(&self.recv_timestamp.0.to_be_bytes());
        buffer[40..48].copy_from_slice(&self.transmit_timestamp.0.to_be_bytes());

        buffer
    }

    pub fn from_bytes(bytes: &[u8]) -> Self {
        let mut packet = NtpPacket::new();
        packet.li_vn_mode = bytes[0];
        packet.stratum = bytes[1];
        packet.poll = bytes[2] as i8;
        packet.precision = bytes[3] as i8;
        packet.root_delay = u32::from_be_bytes([bytes[4], bytes[5], bytes[6], bytes[7]]);
        packet.root_dispersion = u32::from_be_bytes([bytes[8], bytes[9], bytes[10], bytes[11]]);
        packet.ref_id = u32::from_be_bytes([bytes[12], bytes[13], bytes[14], bytes[15]]);
        packet.ref_timestamp = NtpTimestamp(u64::from_be_bytes([
            bytes[16], bytes[17], bytes[18], bytes[19], bytes[20], bytes[21], bytes[22], bytes[23],
        ]));
        packet.origin_timestamp = NtpTimestamp(u64::from_be_bytes([
            bytes[24], bytes[25], bytes[26], bytes[27], bytes[28], bytes[29], bytes[30], bytes[31],
        ]));
        packet.recv_timestamp = NtpTimestamp(u64::from_be_bytes([
            bytes[32], bytes[33], bytes[34], bytes[35], bytes[36], bytes[37], bytes[38], bytes[39],
        ]));
        packet.transmit_timestamp = NtpTimestamp(u64::from_be_bytes([
            bytes[40], bytes[41], bytes[42], bytes[43], bytes[44], bytes[45], bytes[46], bytes[47],
        ]));
        packet
    }
}

/// Convert (diff of) NTP timestamp into Duration. Returns (Duration, is_positive) where is_positive is true if the duration is positive since Duration cannot be negative.
fn to_duration(n: i64) -> (Duration, bool) {
    let n_ = n.abs();
    let secs = n_ >> 32;
    let nsecs = ((n_ & 0xffffffff) * 1_000_000_000) >> 32;
    let dur = Duration::new(secs as u64, nsecs as u32);
    (dur, n >= 0)
}

/// Parse NTP response. Returns delay and offset.
pub(crate) fn parse_response(
    buf: [u8; 48],
    originate_ts: SystemTime,
    destination_ts: SystemTime,
) -> ((Duration, bool), (Duration, bool)) {
    let response = NtpPacket::from_bytes(&buf);

    // assert_eq!(originate_ts, response.origin_timestamp.into());
    // make the assert above a little bit more flexible. allow 10ns difference
    assert!(
        response.origin_timestamp.diff(&originate_ts.into()) < Duration::from_nanos(10),
        "origin timestamp mismatch"
    );

    let ot = response.origin_timestamp.0 as i64;
    let rt = response.recv_timestamp.0 as i64;
    let tt = response.transmit_timestamp.0 as i64;

    // dump ot, rt, tt in bits, spaced by 8 bits
    log::debug!("ot: {:x}", ot);
    log::debug!("rt: {:x}", rt);
    log::debug!("tt: {:x}", tt);

    let ntp_time = response.transmit_timestamp.0 >> 32;
    let unix_time = ntp_time - NTP_TIMESTAMP_DELTA;

    log::debug!("Current NTP time: {}", unix_time);

    let dt = NtpTimestamp::from(destination_ts).0 as i64;
    let d = (dt - ot) - (tt - rt);
    log::debug!("rt - ot: {:?} = {} sec", rt - ot, (rt - ot) >> 32);
    log::debug!("dt - ot: {:?} = {} sec", dt - ot, (dt - ot) >> 32);
    let t = (((rt as i128) - (ot as i128)) + ((tt as i128) - (dt as i128))) / 2;

    let delay = to_duration(d);
    log::debug!("Delay: {:?}", delay);

    let offset = to_duration(t as i64);
    log::debug!("Offset: {:?}", offset);

    log::debug!("Origin time: {:?}", originate_ts);
    log::debug!(
        "Receive time: {:?}",
        SystemTime::from(NtpTimestamp(rt as u64))
    );
    log::debug!(
        "Transmit time: {:?}",
        SystemTime::from(NtpTimestamp(tt as u64))
    );
    log::debug!("Destination time: {:?}", destination_ts);

    let d = to_duration(d);
    let t = to_duration(t as i64); // TODO: fix?
    (d, t)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convert_ntp_to_system_int() {
        let ntp = (NTP_TIMESTAMP_DELTA + 3) << 32;
        let system = SystemTime::from(NtpTimestamp(ntp));
        assert_eq!(system, UNIX_EPOCH + Duration::from_secs(3));
    }

    #[test]
    fn convert_ntp_to_system_frac() {
        let ntp = NTP_TIMESTAMP_DELTA << 32 | 1 << 31;
        let system = SystemTime::from(NtpTimestamp(ntp));
        assert_eq!(system, UNIX_EPOCH + Duration::from_millis(500));
    }

    #[test]
    fn convert_system_to_ntp_int() {
        let system = UNIX_EPOCH + Duration::from_secs(3);
        let ntp = NtpTimestamp::from(system);
        assert_eq!(ntp.0, (NTP_TIMESTAMP_DELTA + 3) << 32);
    }

    #[test]
    fn convert_system_to_ntp_frac() {
        let system = UNIX_EPOCH + Duration::from_millis(500);
        log::debug!("{:?}", system);
        let ntp = NtpTimestamp::from(system);
        log::debug!("left: {:x}", ntp.0);
        log::debug!("right: {:x}", NTP_TIMESTAMP_DELTA << 32 | 1 << 31);
        assert_eq!(ntp.0, NTP_TIMESTAMP_DELTA << 32 | 1 << 31);
    }

    #[test]
    fn convert_epoch_system_to_ntp_frac() {
        let system = UNIX_EPOCH;
        let ntp = NtpTimestamp::from(system);
        assert_eq!(ntp.0, NTP_TIMESTAMP_DELTA << 32);
    }

    #[test]
    fn test_diff() {
        let t1 = UNIX_EPOCH + Duration::from_secs(1);
        let t2 = UNIX_EPOCH + Duration::from_secs(2);
        let ntp1 = NtpTimestamp::from(t1);
        let ntp2 = NtpTimestamp::from(t2);
        let duration = ntp2.diff(&ntp1);
        assert_eq!(duration, Duration::from_secs(1));
    }

    #[test]
    fn test_parse_response() {
        let originate_ts = SystemTime::now();

        let packet = NtpPacket {
            li_vn_mode: 0x1b,
            stratum: 1,
            poll: 4,
            precision: -6,
            root_delay: 0,
            root_dispersion: 0,
            ref_id: 0,
            ref_timestamp: originate_ts.into(),
            origin_timestamp: originate_ts.into(),
            recv_timestamp: (originate_ts + Duration::from_secs(1)).into(),
            transmit_timestamp: (originate_ts + Duration::from_secs(2)).into(),
        };

        log::debug!("{:?}", packet.origin_timestamp.0);
        log::debug!("{:?}", packet.recv_timestamp.0);
        log::debug!("{:?}", packet.transmit_timestamp.0);

        let buf = packet.to_bytes();
        let destination_ts = originate_ts + Duration::from_secs(3);
        let (delay, offset) = parse_response(buf, originate_ts, destination_ts);

        log::debug!("Delay: {:?}", delay);
        log::debug!("Offset: {:?}", offset);

        assert_eq!(delay, Duration::from_secs(2));
        assert_eq!(offset, Duration::from_secs(0));
    }
}
