/// Command Block Wrapper — USB MSC BOT §5.1. Always 31 bytes on the wire.
#[repr(C, packed)]
#[derive(Copy, Clone)]
pub struct Cbw {
    pub signature: u32,
    pub tag: u32,
    pub data_transfer_length: u32,
    pub flags: u8,
    pub lun: u8,
    pub cb_length: u8,
    pub cb: [u8; 16],
}

pub const CBW_SIGNATURE: u32 = 0x4342_5355; // "USBC"
pub const CBW_FLAGS_IN: u8 = 0x80;
pub const CBW_WIRE_LEN: usize = 31;

impl Default for Cbw {
    fn default() -> Self {
        Cbw {
            signature: CBW_SIGNATURE,
            tag: 1,
            data_transfer_length: 0,
            flags: 0,
            lun: 0,
            cb_length: 0,
            cb: [0u8; 16],
        }
    }
}

/// Command Status Wrapper — USB MSC BOT §5.2. Always 13 bytes on the wire.
#[repr(C, packed)]
#[derive(Copy, Clone, Default)]
pub struct Csw {
    pub signature: u32,
    pub tag: u32,
    pub data_residue: u32,
    pub status: u8,
}

pub const CSW_SIGNATURE: u32 = 0x5342_5355; // "USBS"
pub const CSW_STATUS_PASS: u8 = 0;
pub const CSW_WIRE_LEN: usize = 13;

/// Serialize a CBW into the first 31 bytes of `buf`.
pub fn write_cbw(buf: &mut [u8], cbw: &Cbw) {
    buf[0..4].copy_from_slice(&cbw.signature.to_le_bytes());
    buf[4..8].copy_from_slice(&cbw.tag.to_le_bytes());
    buf[8..12].copy_from_slice(&cbw.data_transfer_length.to_le_bytes());
    buf[12] = cbw.flags;
    buf[13] = cbw.lun;
    buf[14] = cbw.cb_length;
    buf[15..31].copy_from_slice(&cbw.cb);
}

/// Deserialize a CSW from the first 13 bytes of `buf`.
pub fn read_csw(buf: &[u8]) -> Csw {
    Csw {
        signature: u32::from_le_bytes([buf[0], buf[1], buf[2], buf[3]]),
        tag: u32::from_le_bytes([buf[4], buf[5], buf[6], buf[7]]),
        data_residue: u32::from_le_bytes([buf[8], buf[9], buf[10], buf[11]]),
        status: buf[12],
    }
}

/// SCSI INQUIRY CDB — 36-byte standard response.
pub fn scsi_inquiry_cdb() -> [u8; 16] {
    let mut cdb = [0u8; 16];
    cdb[0] = 0x12;
    cdb[4] = 36;
    cdb
}

/// SCSI READ CAPACITY(10) CDB — 8-byte response: last LBA + block length.
pub fn scsi_read_capacity_cdb() -> [u8; 16] {
    let mut cdb = [0u8; 16];
    cdb[0] = 0x25;
    cdb
}

/// SCSI READ(10) CDB — read `count` sectors from `lba`.
pub fn scsi_read10_cdb(lba: u32, count: u16) -> [u8; 16] {
    let mut cdb = [0u8; 16];
    cdb[0] = 0x28;
    cdb[2] = (lba >> 24) as u8;
    cdb[3] = (lba >> 16) as u8;
    cdb[4] = (lba >> 8) as u8;
    cdb[5] = lba as u8;
    cdb[7] = (count >> 8) as u8;
    cdb[8] = count as u8;
    cdb
}
