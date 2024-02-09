use alloc::{borrow::Cow, boxed::Box};
use awkernel_lib::interrupt::IRQ;

use crate::pcie::{BaseAddress, PCIeDeviceErr, PCIeInfo};

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
pub struct Msix {
    base: usize,
    table_size: u16, // N - 1

    table_offset: u32, // Table offset
    table_bar: BaseAddress,

    _pba_offset: u32, // Pending Bit
    _pba_bar: BaseAddress,
}

impl Msix {
    pub fn new(info: &PCIeInfo, base: usize) -> Option<Self> {
        let table_size = ((registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.read(base) >> 16)
            & 0b0111_1111_1111) as u16;

        let table_offset = registers::MSIX_TABLE_OFFSET.read(base);
        let table_bir = (table_offset & 0b111) as u8;
        let table_offset = table_offset & !0b111;

        let table_bar = info.get_bar(table_bir as usize)?;

        let pba_offset = registers::MSIX_PBA_OFFSET.read(base);
        let pba_bir = (pba_offset & 0b111) as u8;
        let pba_offset = pba_offset & !0b111;

        let pba_bar = info.get_bar(pba_bir as usize)?;

        Some(Self {
            base,
            table_size,
            table_offset,
            table_bar,
            _pba_offset: pba_offset,
            _pba_bar: pba_bar,
        })
    }

    pub fn disable(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.clrbits(registers::CTRL_ENABLE, self.base);
    }

    pub fn enable(&mut self) {
        registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID.setbits(registers::CTRL_ENABLE, self.base);
    }

    pub fn register_handler<F>(
        &mut self,
        name: Cow<'static, str>,
        func: Box<F>,
        segment_number: usize,
        target: u32,
        msi_x_entry: usize,
    ) -> Result<IRQ, PCIeDeviceErr>
    where
        F: Fn(u16) + Send + 'static,
    {
        if self.table_size as usize <= msi_x_entry {
            return Err(PCIeDeviceErr::Interrupt);
        }

        let mut message_address = 0;
        let mut message_address_upper = 0;
        let mut message_data = 0;

        let irq = awkernel_lib::interrupt::register_handler_pcie_msi(
            name,
            func,
            segment_number,
            target,
            &mut message_data,
            &mut message_address,
            Some(&mut message_address_upper),
        )
        .or(Err(PCIeDeviceErr::Interrupt))?;

        let offset = 16 * msi_x_entry + self.table_offset as usize;

        self.table_bar.write32(offset, message_address);
        self.table_bar.write32(offset + 4, message_address_upper);
        self.table_bar.write32(offset + 8, message_data);
        self.table_bar.write32(offset + 12, 0);

        Ok(irq)
    }
}
