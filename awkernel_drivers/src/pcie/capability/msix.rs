use crate::pcie::{BaseAddress, PCIeInfo};

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
    table_size: u16, // N - 1

    table_offset: u32, // Table offset
    table_bar: BaseAddress,

    pba_offset: u32, // Pending Bit
    pba_bar: BaseAddress,
}

// Intel e1000e driver has been initialized. IRQ = Some(64),
// Info = DeviceInfo { addr: 2952855552, bus: 0, id: 4307, vendor: 32902, device_name: Some(Intel82574GbE),
// _multiple_functions: false, header_type: 0, base_addresses: [MMIO { addr: 3238658048, size: 131072, address_type: T32B, prefetchable: false }, MMIO { addr: 3238526976, size: 131072, address_type: T32B, prefetchable: false }, IO(24672), MMIO { addr: 3238789120, size: 16384, address_type: T32B, prefetchable: false }, None, None],
// msi: Some(
//      MSI {
//          cap_ptr: 2952855760,
//          multiple_message_capable: One,
//          per_vector_mask_capable: false,
//          bit64_address_capable: true }),
// msix: Some(
//      MSIX {
//          cap_ptr: 2952855712,
//          table_size: 4,
//          table_offset: 0,
//          table_bar: MMIO { addr: 3238789120, size: 16384, address_type: T32B, prefetchable: false },
//          pba_offset: 8192, pba_bar: MMIO { addr: 3238789120, size: 16384, address_type: T32B, prefetchable: false } }) }

impl MSIX {
    pub fn new(info: &PCIeInfo, cap_ptr: usize) -> Option<Self> {
        let table_size = ((registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(cap_ptr) >> 16)
            & 0b0111_1111_1111) as u16;

        let table_offset = registers::MSIX_TABLE_OFFSET.read(cap_ptr);
        let table_bir = (table_offset & 0b111) as u8;
        let table_offset = table_offset & !0b111;

        let table_bar = info.get_bar(table_bir as usize)?;

        let pba_offset = registers::MSIX_PBA_OFFSET.read(cap_ptr);
        let pba_bir = (pba_offset & 0b111) as u8;
        let pba_offset = pba_offset & !0b111;

        let pba_bar = info.get_bar(pba_bir as usize)?;

        Some(Self {
            cap_ptr,
            table_size,
            table_offset,
            table_bar,
            pba_offset,
            pba_bar,
        })
    }

    pub fn disalbe(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.clrbits(registers::CTRL_ENABLE, self.cap_ptr);
    }
}
