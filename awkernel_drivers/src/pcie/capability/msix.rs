use alloc::{borrow::Cow, boxed::Box, format, string::String};
use awkernel_lib::interrupt::IRQ;

use crate::pcie::{BaseAddress, ConfigSpace, PCIeDeviceErr, PCIeInfo};

mod registers {
    pub const MESSAGE_CONTROL_NEXT_PTR_CAP_ID: usize = 0;

    // Message Control Register
    pub const CTRL_ENABLE: u32 = 1 << 31;

    // MSI-X
    pub const MSIX_TABLE_OFFSET: usize = 0x04;
    pub const MSIX_PBA_OFFSET: usize = 0x08; // Pending Bit Array
}

#[derive(Debug)]
pub struct Msix {
    cap_ptr: usize,
    config_space: ConfigSpace,
    table_size: u16, // N - 1

    table_offset: u32, // Table offset
    table_bar: BaseAddress,

    pba_offset: u32, // Pending Bit
    pba_bar: BaseAddress,
}

impl Msix {
    pub fn new(info: &PCIeInfo, cap_ptr: usize) -> Option<Self> {
        let config_space = info.config_space.clone();

        let table_size =
            ((config_space.read_u32(cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID) >> 16)
                & 0b0111_1111_1111) as u16;

        let table_offset = config_space.read_u32(cap_ptr + registers::MSIX_TABLE_OFFSET);
        let table_bir = (table_offset & 0b111) as u8;
        let table_offset = table_offset & !0b111;

        let table_bar = info.get_bar(table_bir as usize)?;

        let pba_offset = config_space.read_u32(cap_ptr + registers::MSIX_PBA_OFFSET);
        let pba_bir = (pba_offset & 0b111) as u8;
        let pba_offset = pba_offset & !0b111;

        let pba_bar = info.get_bar(pba_bir as usize)?;

        Some(Self {
            cap_ptr,
            config_space,
            table_size,
            table_offset,
            table_bar,
            pba_offset,
            pba_bar,
        })
    }

    pub fn dump(&self, info: &PCIeInfo) -> String {
        let header = info.config_space.read_u32(self.cap_ptr);
        let table_offset = info.config_space.read_u32(self.cap_ptr + 4);
        let pending_bit_array_offset = info.config_space.read_u32(self.cap_ptr + 8);
        let mut msg = format!("MSI-X Capability:\r\n    header: {header:#08x}\r\n    table offset: {table_offset:#08x}\r\n    pending bit array offset: {pending_bit_array_offset:#08x}\r\n");

        msg = format!("{msg}MSI-X Table:\r\n");
        for i in 0..=self.table_size {
            let offset = 16 * i as usize + self.table_offset as usize;
            let addr = self.table_bar.read32(offset).unwrap_or(0);
            let addr_upper = self.table_bar.read32(offset + 4).unwrap_or(0);
            let data = self.table_bar.read32(offset + 8).unwrap_or(0);
            let vector_control = self.table_bar.read32(offset + 12).unwrap_or(0);
            msg = format!("{msg}    [{i}] addr: {addr:#08x}, addr_upper: {addr_upper:#08x}, data: {data:#08x}, vector_control: {vector_control:#08x}\r\n");
        }

        msg = format!("{msg}MSI-X Pending Bit Array:\r\n");
        for i in 0..=(self.table_size / 64) {
            let offset = 8 * i as usize + self.pba_offset as usize;

            let lower32 = self.pba_bar.read32(offset).unwrap_or(0);
            let upper32 = self.pba_bar.read32(offset + 4).unwrap_or(0);
            let pba = ((upper32 as u64) << 32) | (lower32 as u64);
            msg = format!("{msg}    [{i}] {pba:#016x}\r\n");
        }

        msg
    }

    pub fn disable(&mut self) {
        let reg = self
            .config_space
            .read_u32(registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID);
        self.config_space.write_u32(
            reg & !registers::CTRL_ENABLE,
            self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID,
        );
    }

    pub fn enable(&mut self) {
        let reg = self
            .config_space
            .read_u32(registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID);
        self.config_space.write_u32(
            reg | registers::CTRL_ENABLE,
            self.cap_ptr + registers::MESSAGE_CONTROL_NEXT_PTR_CAP_ID,
        );
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
        // Because the table size in the config space represents the number of entries minus one,
        // `self.table_size == msi_x_entry` is valid.
        if (self.table_size as usize) < msi_x_entry {
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

    /// Returns the size of the MSI-X table.
    /// Because the table size in the config space represents the number of entries minus one,
    /// this method returns `table_size + 1`.
    pub fn get_table_size(&self) -> u16 {
        self.table_size + 1
    }
}
