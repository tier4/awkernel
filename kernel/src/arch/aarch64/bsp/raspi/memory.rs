use crate::{mmio_rw, mmio_w};

//-----------------------------------------------------------------------------
// Raspberry Pi 3
#[cfg(feature = "raspi3")]
mod raspi {
    pub(super) const MMIO_BASE: usize = 0x3F000000;
    pub(super) const DEVICE_MEM_START: u64 = 0x3C000000;
    pub(super) const DEVICE_MEM_END: u64 = 0x40000000;
}
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Raspberry Pi 4
#[cfg(feature = "raspi4")]
mod raspi {
    pub(super) const MMIO_BASE: usize = 0xfe000000;
    pub(super) const DEVICE_MEM_START: u64 = 0xfd500000;
    pub(super) const DEVICE_MEM_END: u64 = 0xff000000;
}
//-----------------------------------------------------------------------------

pub const SRAM_START: u64 = 0;
pub const SRAM_END: u64 = 0;
pub const ROM_START: u64 = 0;
pub const ROM_END: u64 = 0;
pub const DRAM_BASE: u64 = 0;

pub const MMIO_BASE: usize = raspi::MMIO_BASE;
pub const DEVICE_MEM_START: u64 = raspi::DEVICE_MEM_START;
pub const DEVICE_MEM_END: u64 = raspi::DEVICE_MEM_END;

const GPIO_BASE: usize = MMIO_BASE + 0x00200000;

mmio_rw!(GPIO_BASE         => pub gpfsel0<u32>);
mmio_rw!(GPIO_BASE + 0x004 => pub gpfsel1<u32>);
mmio_rw!(GPIO_BASE + 0x008 => pub gpfsel2<u32>);
mmio_rw!(GPIO_BASE + 0x00c => pub gpfsel3<u32>);
mmio_rw!(GPIO_BASE + 0x010 => pub gpfsel4<u32>);
mmio_rw!(GPIO_BASE + 0x014 => pub gpfsel5<u32>);
mmio_w! (GPIO_BASE + 0x01c => pub gpset0<u32>);
mmio_w! (GPIO_BASE + 0x020 => pub gpset1<u32>);
mmio_w! (GPIO_BASE + 0x028 => pub gpclr0<u32>);
mmio_w! (GPIO_BASE + 0x02c => pub gpclr1<u32>);
mmio_w! (GPIO_BASE + 0x034 => pub gplev0<u32>);
mmio_w! (GPIO_BASE + 0x038 => pub gplev1<u32>);
mmio_rw!(GPIO_BASE + 0x040 => pub gpeds0<u32>);
mmio_rw!(GPIO_BASE + 0x044 => pub gpeds1<u32>);
mmio_rw!(GPIO_BASE + 0x04c => pub gpren0<u32>);
mmio_rw!(GPIO_BASE + 0x050 => pub gpren1<u32>);
mmio_rw!(GPIO_BASE + 0x058 => pub gpfen0<u32>);
mmio_rw!(GPIO_BASE + 0x05c => pub gpfen1<u32>);
mmio_rw!(GPIO_BASE + 0x064 => pub gphen0<u32>);
mmio_rw!(GPIO_BASE + 0x068 => pub gphen1<u32>);
mmio_rw!(GPIO_BASE + 0x070 => pub gplen0<u32>);
mmio_rw!(GPIO_BASE + 0x074 => pub gplen1<u32>);
mmio_rw!(GPIO_BASE + 0x07c => pub gparen0<u32>);
mmio_rw!(GPIO_BASE + 0x080 => pub gparen1<u32>);
mmio_rw!(GPIO_BASE + 0x088 => pub gpafen0<u32>);
mmio_rw!(GPIO_BASE + 0x08c => pub gpafen1<u32>);
mmio_rw!(GPIO_BASE + 0x094 => pub gppud<u32>);
mmio_rw!(GPIO_BASE + 0x098 => pub gppudclk0<u32>);
mmio_rw!(GPIO_BASE + 0x09c => pub gppudclk1<u32>);

pub const UART0_BASE: usize = MMIO_BASE + 0x00201000;
