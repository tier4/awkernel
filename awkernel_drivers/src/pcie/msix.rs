mod registers {
    use awkernel_lib::{mmio_r, mmio_rw};

    mmio_rw!(offset 0x00 => pub MESSAGE_CONTROL_NEXT_PTR_CAP_ID<u32>);

    // MSI

    // Message Control Register
    pub const MSI_ENABLE: u32 = 1 << 16;
    pub const MSI_BIT64_ADDRESS_CAPABLE: u32 = 1 << (7 + 16);
    pub const MSI_PER_VECTOR_MASK_CAPABLE: u32 = 1 << (8 + 16);

    // MSI-X
    mmio_r!(offset 0x04 => pub MSIX_TABLE_OFFSET<u32>);
    mmio_r!(offset 0x04 => pub MSIX_PBA_OFFSET<u32>); // Pending Bit Array
}

pub struct MSIX {
    base: usize,
    table_size: u16, // N - 1
    table_offset: u32,
    table_bir: u8, // Table BAR indicator
    pba_offset: u32,
    pba_bir: u8, // PBAR BAR indicator
}

impl MSIX {
    pub fn new(cap_ptr: usize) -> Self {
        let base = cap_ptr;
        let table_size = ((registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(base) >> 16)
            & 0b0111_1111_1111) as u16;

        let table_offset = registers::MSIX_TABLE_OFFSET.read(base);
        let table_bir = (table_offset & 0b111) as u8;
        let table_offset = table_offset & !0b111;

        let pba_offset = registers::MSIX_PBA_OFFSET.read(base);
        let pba_bir = (pba_offset & 0b111) as u8;
        let pba_offset = pba_offset & !0b111;

        log::debug!("MSIX: table_size = {}", table_size);

        Self {
            base,
            table_size,
            table_offset,
            table_bir,
            pba_offset,
            pba_bir,
        }
    }
}
