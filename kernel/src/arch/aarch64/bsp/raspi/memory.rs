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
    pub(super) const MMIO_BASE: usize = 0xFE000000;
    pub(super) const DEVICE_MEM_START: u64 = 0x0fd000000; // maybe...
    pub(super) const DEVICE_MEM_END: u64 = 0x100000000; // maybe...
}
//-----------------------------------------------------------------------------

pub(super) const SRAM_START: u64 = 0;
pub(super) const SRAM_END: u64 = 0;
pub(super) const ROM_START: u64 = 0;
pub(super) const ROM_END: u64 = 0;
pub(super) const DRAM_BASE: u64 = 0;

pub(super) const MMIO_BASE: usize = raspi::MMIO_BASE;
pub(super) const DEVICE_MEM_START: u64 = raspi::DEVICE_MEM_START;
pub(super) const DEVICE_MEM_END: u64 = raspi::DEVICE_MEM_END;

const GPIO_BASE: usize = MMIO_BASE + 0x00200000;

mmio_rw!(GPIO_BASE         => pub(super) gpfsel0<u32>);
mmio_rw!(GPIO_BASE + 0x004 => pub(super) gpfsel1<u32>);
mmio_rw!(GPIO_BASE + 0x008 => pub(super) gpfsel2<u32>);
mmio_rw!(GPIO_BASE + 0x00c => pub(super) gpfsel3<u32>);
mmio_rw!(GPIO_BASE + 0x010 => pub(super) gpfsel4<u32>);
mmio_rw!(GPIO_BASE + 0x014 => pub(super) gpfsel5<u32>);
mmio_w! (GPIO_BASE + 0x01c => pub(super) gpset0<u32>);
mmio_w! (GPIO_BASE + 0x020 => pub(super) gpset1<u32>);
mmio_w! (GPIO_BASE + 0x028 => pub(super) gpclr0<u32>);
mmio_w! (GPIO_BASE + 0x02c => pub(super) gpclr1<u32>);
mmio_w! (GPIO_BASE + 0x034 => pub(super) gplev0<u32>);
mmio_w! (GPIO_BASE + 0x038 => pub(super) gplev1<u32>);
mmio_rw!(GPIO_BASE + 0x040 => pub(super) gpeds0<u32>);
mmio_rw!(GPIO_BASE + 0x044 => pub(super) gpeds1<u32>);
mmio_rw!(GPIO_BASE + 0x04c => pub(super) gpren0<u32>);
mmio_rw!(GPIO_BASE + 0x050 => pub(super) gpren1<u32>);
mmio_rw!(GPIO_BASE + 0x058 => pub(super) gpfen0<u32>);
mmio_rw!(GPIO_BASE + 0x05c => pub(super) gpfen1<u32>);
mmio_rw!(GPIO_BASE + 0x064 => pub(super) gphen0<u32>);
mmio_rw!(GPIO_BASE + 0x068 => pub(super) gphen1<u32>);
mmio_rw!(GPIO_BASE + 0x070 => pub(super) gplen0<u32>);
mmio_rw!(GPIO_BASE + 0x074 => pub(super) gplen1<u32>);
mmio_rw!(GPIO_BASE + 0x07c => pub(super) gparen0<u32>);
mmio_rw!(GPIO_BASE + 0x080 => pub(super) gparen1<u32>);
mmio_rw!(GPIO_BASE + 0x088 => pub(super) gpafen0<u32>);
mmio_rw!(GPIO_BASE + 0x08c => pub(super) gpafen1<u32>);
mmio_rw!(GPIO_BASE + 0x094 => pub(super) gppud<u32>);
mmio_rw!(GPIO_BASE + 0x098 => pub(super) gppudclk0<u32>);
mmio_rw!(GPIO_BASE + 0x09c => pub(super) gppudclk1<u32>);
