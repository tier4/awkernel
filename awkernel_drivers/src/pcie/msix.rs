mod registers {
    use awkernel_lib::{mmio_r, mmio_rw};

    mmio_rw!(offset 0x00 => pub MESSAGE_CONTROL_NEXT_PTR_CAP_ID<u32>);

    // Message Control Register
    pub const CTRL_ENABLE: u32 = 1 << 31;

    // MSI-X
    mmio_r!(offset 0x04 => pub MSIX_TABLE_OFFSET<u32>);
    mmio_r!(offset 0x08 => pub MSIX_PBA_OFFSET<u32>); // Pending Bit Array
}

#[derive(Debug)]
pub struct MSIX {
    cap_ptr: usize,
    table_size: u16,   // N - 1
    table_offset: u32, // Table offset
    table_bir: u8,     // Table BAR indicator
    pba_offset: u32,   // Pending Bit
    pba_bir: u8,       // PBAR BAR indicator
}

impl MSIX {
    pub fn new(cap_ptr: usize) -> Self {
        let table_size = ((registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(cap_ptr) >> 16)
            & 0b0111_1111_1111) as u16;

        let table_offset = registers::MSIX_TABLE_OFFSET.read(cap_ptr);
        let table_bir = (table_offset & 0b111) as u8;
        let table_offset = table_offset & !0b111;

        let pba_offset = registers::MSIX_PBA_OFFSET.read(cap_ptr);
        let pba_bir = (pba_offset & 0b111) as u8;
        let pba_offset = pba_offset & !0b111;

        log::debug!("MSIX: table_size = {}", table_size);

        Self {
            cap_ptr,
            table_size,
            table_offset,
            table_bir,
            pba_offset,
            pba_bir,
        }
    }

    pub fn disalbe(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.clrbits(registers::CTRL_ENABLE, self.cap_ptr);
    }
}
