use super::SystemTime;
use core::{fmt::Display, ops::Sub, time::Duration};

pub const NTP_TIMESTAMP_DELTA: u64 = 2_208_988_800; // seconds between 1900 and 1970

static UNIX_EPOCH: SystemTime = SystemTime::epoch();

/// NTP timestamp in 64-bit fixed-point format. The first 32 bits represent the number of seconds since 1900, and the last 32 bits represent the fraction of a second.
#[derive(Debug, Copy, Clone)]
pub struct NtpTimestamp(pub u64);

impl NtpTimestamp {
    /// Calculate the difference `self - other`. The first value is the difference in time, and the second value is true if `self` is greater than `other`.
    pub fn diff(&self, other: &Self) -> (Duration, bool) {
        if self.0 > other.0 {
            let diff = self.0 - other.0;
            let secs = diff >> 32;
            let nsecs = ((diff & 0xffffffff) * 1_000_000_000) >> 32;
            (Duration::new(secs as u64, nsecs as u32), true)
        } else {
            let diff = other.0 - self.0;
            let secs = diff >> 32;
            let nsecs = ((diff & 0xffffffff) * 1_000_000_000) >> 32;
            (Duration::new(secs as u64, nsecs as u32), false)
        }
    }

    pub fn from_epoch_us(us: u64) -> Self {
        let secs = us / 1_000_000;
        let nsecs = ((us % 1_000_000) * 1_000) as u32;
        NtpTimestamp((NTP_TIMESTAMP_DELTA + secs) << 32 | nsecs as u64)
    }
}

impl Display for NtpTimestamp {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
        let secs = self.0 >> 32;
        let nsecs = ((self.0 & 0xffffffff) * 1_000_000_000) >> 32;
        write!(f, "{}.{:09}", secs, nsecs)
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

impl Sub for NtpTimestamp {
    type Output = (Duration, bool);

    fn sub(self, rhs: Self) -> Self::Output {
        self.diff(&rhs)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn convert_ntp_to_system_int() {
        let ntp = (NTP_TIMESTAMP_DELTA + 3) << 32;
        let system = SystemClock::from(NtpTimestamp(ntp));
        assert_eq!(system, UNIX_EPOCH + Duration::from_secs(3));
    }

    #[test]
    fn convert_ntp_to_system_frac() {
        let ntp = NTP_TIMESTAMP_DELTA << 32 | 1 << 31;
        let system = SystemClock::from(NtpTimestamp(ntp));
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
        let originate_ts = SystemClock::now();

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
