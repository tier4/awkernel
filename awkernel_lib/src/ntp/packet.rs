use core::time::Duration;

use crate::ntp::{timestamp::NTP_TIMESTAMP_DELTA, SystemTime};

use super::timestamp::NtpTimestamp;

#[derive(Debug)]
pub struct NtpPacket {
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

    /// Parse NTP response. Returns delay and offset.
    pub fn parse_response(
        &self,
        originate_ts: NtpTimestamp,
        destination_ts: NtpTimestamp,
    ) -> ((Duration, bool), (Duration, bool)) {
        log::debug!(
            "diff: {:?}",
            self.origin_timestamp.diff(&originate_ts.into())
        );
        // us vs ns
        log::debug!("given: {} {:?}", originate_ts, originate_ts);
        log::debug!(
            "self: {} {:?}",
            self.origin_timestamp,
            self.origin_timestamp
        );
        // Ideally originate_ts should be equal to self.origin_timestamp but here we allow 10ns difference
        assert!(
            self.origin_timestamp.diff(&originate_ts.into()).0 < Duration::from_nanos(10),
            "origin timestamp mismatch"
        );

        let ot = self.origin_timestamp.0 as i64;
        let rt = self.recv_timestamp.0 as i64;
        let tt = self.transmit_timestamp.0 as i64;

        // dump ot, rt, tt in bits, spaced by 8 bits
        log::debug!("ot: {:x}", ot);
        log::debug!("rt: {:x}", rt);
        log::debug!("tt: {:x}", tt);

        let ntp_time = self.transmit_timestamp.0 >> 32;
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
        log::debug!("Receive time: {:?}", SystemTime::from(self.recv_timestamp));
        log::debug!(
            "Transmit time: {:?}",
            SystemTime::from(self.transmit_timestamp)
        );
        log::debug!("Destination time: {:?}", destination_ts);

        (delay, offset)
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
