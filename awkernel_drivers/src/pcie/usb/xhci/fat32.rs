pub const EOC: u32 = 0x0FFF_FFF8;
pub const DIRENT_SIZE: usize = 32;
pub const ATTR_LFN: u8 = 0x0F;
pub const ATTR_DIR: u8 = 0x10;
pub const ATTR_VOLUME: u8 = 0x08;

/// FAT32 volume metadata decoded from the BPB.
pub struct Fat32 {
    pub partition_lba: u32,
    pub bytes_per_sec: u16,
    pub sec_per_clus: u8,
    pub rsvd_sec: u32,
    pub num_fats: u8,
    pub fat_sz: u32,
    pub root_clus: u32,
    pub first_data_sec: u32,
}

impl Fat32 {
    pub fn from_bpb(buf: &[u8], partition_lba: u32) -> Option<Self> {
        if buf.len() < 90 { return None; }
        let bytes_per_sec = u16::from_le_bytes([buf[11], buf[12]]);
        let sec_per_clus  = buf[13];
        let rsvd_sec      = u32::from(u16::from_le_bytes([buf[14], buf[15]]));
        let num_fats      = buf[16];
        let fat_sz16      = u32::from(u16::from_le_bytes([buf[22], buf[23]]));
        let fat_sz32      = u32::from_le_bytes([buf[36], buf[37], buf[38], buf[39]]);
        let fat_sz        = if fat_sz16 != 0 { fat_sz16 } else { fat_sz32 };
        let root_clus     = u32::from_le_bytes([buf[44], buf[45], buf[46], buf[47]]);
        if bytes_per_sec == 0 || sec_per_clus == 0 || fat_sz == 0 { return None; }
        let first_data_sec = rsvd_sec + num_fats as u32 * fat_sz;
        Some(Fat32 { partition_lba, bytes_per_sec, sec_per_clus, rsvd_sec,
                     num_fats, fat_sz, root_clus, first_data_sec })
    }

    /// Absolute LBA of the first sector in `cluster`.
    pub fn cluster_to_lba(&self, cluster: u32) -> u32 {
        self.partition_lba + self.first_data_sec + (cluster - 2) * self.sec_per_clus as u32
    }

    /// (absolute_lba, byte_offset_within_sector) of the FAT32 entry for `cluster`.
    pub fn fat_entry_pos(&self, cluster: u32) -> (u32, usize) {
        let byte_off = cluster * 4;
        let sec = self.partition_lba + self.rsvd_sec + byte_off / self.bytes_per_sec as u32;
        let off = (byte_off % self.bytes_per_sec as u32) as usize;
        (sec, off)
    }
}

/// Extract 13 UTF-16LE code units from an LFN directory entry.
pub fn lfn_chars(entry: &[u8]) -> [u16; 13] {
    let mut out = [0xFFFFu16; 13];
    for i in 0..5  { out[i]    = u16::from_le_bytes([entry[1+i*2],  entry[2+i*2]]); }
    for i in 0..6  { out[5+i]  = u16::from_le_bytes([entry[14+i*2], entry[15+i*2]]); }
    for i in 0..2  { out[11+i] = u16::from_le_bytes([entry[28+i*2], entry[29+i*2]]); }
    out
}

/// Extract (first_cluster, file_size) from a normal 32-byte directory entry.
pub fn dir_entry_info(entry: &[u8]) -> (u32, u32) {
    let hi   = u32::from(u16::from_le_bytes([entry[20], entry[21]]));
    let lo   = u32::from(u16::from_le_bytes([entry[26], entry[27]]));
    let size = u32::from_le_bytes([entry[28], entry[29], entry[30], entry[31]]);
    ((hi << 16) | lo, size)
}

/// Case-insensitive 8.3 name comparison.  `entry` is the raw 11-byte name field.
/// `needle` may contain a '.' separator (e.g. "kernel.elf").
pub fn match_83(entry: &[u8], needle: &str) -> bool {
    let nb = needle.as_bytes();
    let dot = nb.iter().rposition(|&c| c == b'.');
    let (name_b, ext_b) = match dot {
        Some(d) => (&nb[..d], &nb[d+1..]),
        None    => (nb, &[][..]),
    };
    if name_b.len() > 8 || ext_b.len() > 3 { return false; }
    for i in 0..8 {
        let e = entry[i];
        let n = if i < name_b.len() { name_b[i].to_ascii_uppercase() } else { b' ' };
        if e != n { return false; }
    }
    for i in 0..3 {
        let e = entry[8+i];
        let n = if i < ext_b.len() { ext_b[i].to_ascii_uppercase() } else { b' ' };
        if e != n { return false; }
    }
    true
}

/// Case-insensitive LFN match.  `buf` is filled by `(seq-1)*13` indexing;
/// comparison stops at the first NUL or 0xFFFF code unit.
pub fn lfn_matches(buf: &[u16; 260], needle: &str) -> bool {
    let mut ascii = [0u8; 260];
    let mut len = 0;
    for &c in buf.iter() {
        if c == 0 || c == 0xFFFF { break; }
        ascii[len] = if c < 128 { c as u8 } else { b'?' };
        len += 1;
    }
    match core::str::from_utf8(&ascii[..len]) {
        Ok(s) => s.eq_ignore_ascii_case(needle),
        Err(_) => false,
    }
}
