use awkernel_lib::{mmio_rw, mmio_w};

//-----------------------------------------------------------------------------
// Raspberry Pi 3
#[cfg(feature = "raspi3")]
mod raspi {
    pub const MMIO_BASE: usize = 0x3F000000;
    pub const DEVICE_MEM_START: u64 = 0x3C000000;
    pub const DEVICE_MEM_END: u64 = 0x40000000;

    pub const INTERRUPT_CTRL_BASE: usize = MMIO_BASE + 0xB200;
}
//-----------------------------------------------------------------------------

//-----------------------------------------------------------------------------
// Raspberry Pi 4
#[cfg(feature = "raspi4")]
mod raspi {
    pub const MMIO_BASE: usize = 0xfe000000;
    pub const DEVICE_MEM_START: u64 = 0xfd500000;
    pub const DEVICE_MEM_END: u64 = 0x100000000;

    pub const INTERRUPT_CTRL_BASE: usize = 0xff800000;
    pub const GIC_V2_DISTRIBUTOR_BASE: usize = INTERRUPT_CTRL_BASE + 0x00041000;
    pub const GIC_V2_CPU_INTERFACE_BASE: usize = INTERRUPT_CTRL_BASE + 0x00042000;
    pub const _GIC_V2_HYPERVISOR_BASE: usize = INTERRUPT_CTRL_BASE + 0x00044000;
    pub const _GIC_V2_VIRTUAL_CPU_BASE: usize = INTERRUPT_CTRL_BASE + 0x00046000;
}
//-----------------------------------------------------------------------------

pub use raspi::*;

pub const SRAM_START: u64 = 0;
pub const SRAM_END: u64 = 0;
pub const ROM_START: u64 = 0;
pub const ROM_END: u64 = 0;
pub const _DRAM_BASE: u64 = 0;

const GPIO_BASE: usize = MMIO_BASE + 0x00200000;

mmio_rw!(GPIO_BASE         => pub GPFSEL0<u32>);
mmio_rw!(GPIO_BASE + 0x004 => pub GPFSEL1<u32>);
mmio_rw!(GPIO_BASE + 0x008 => pub GPFSEL2<u32>);
mmio_rw!(GPIO_BASE + 0x00c => pub GPFSEL3<u32>);
mmio_rw!(GPIO_BASE + 0x010 => pub GPFSEL4<u32>);
mmio_rw!(GPIO_BASE + 0x014 => pub GPFSEL5<u32>);
mmio_w! (GPIO_BASE + 0x01c => pub GPSET0<u32>);
mmio_w! (GPIO_BASE + 0x020 => pub GPSET1<u32>);
mmio_w! (GPIO_BASE + 0x028 => pub GPCLR0<u32>);
mmio_w! (GPIO_BASE + 0x02c => pub GPCLR1<u32>);
mmio_w! (GPIO_BASE + 0x034 => pub GPLEV0<u32>);
mmio_w! (GPIO_BASE + 0x038 => pub GPLEV1<u32>);
mmio_rw!(GPIO_BASE + 0x040 => pub GPEDS0<u32>);
mmio_rw!(GPIO_BASE + 0x044 => pub GPEDS1<u32>);
mmio_rw!(GPIO_BASE + 0x04c => pub GPREN0<u32>);
mmio_rw!(GPIO_BASE + 0x050 => pub GPREN1<u32>);
mmio_rw!(GPIO_BASE + 0x058 => pub GPFEN0<u32>);
mmio_rw!(GPIO_BASE + 0x05c => pub GPFEN1<u32>);
mmio_rw!(GPIO_BASE + 0x064 => pub GPHEN0<u32>);
mmio_rw!(GPIO_BASE + 0x068 => pub GPHEN1<u32>);
mmio_rw!(GPIO_BASE + 0x070 => pub GPLEN0<u32>);
mmio_rw!(GPIO_BASE + 0x074 => pub GPLEN1<u32>);
mmio_rw!(GPIO_BASE + 0x07c => pub GPAREN0<u32>);
mmio_rw!(GPIO_BASE + 0x080 => pub GPAREN1<u32>);
mmio_rw!(GPIO_BASE + 0x088 => pub GPAFEN0<u32>);
mmio_rw!(GPIO_BASE + 0x08c => pub GPAFEN1<u32>);
mmio_rw!(GPIO_BASE + 0x094 => pub GPPUD<u32>);
mmio_rw!(GPIO_BASE + 0x098 => pub GPPUDCLK0<u32>);
mmio_rw!(GPIO_BASE + 0x09c => pub GPPUDCLK1<u32>);

pub const UART0_BASE: usize = MMIO_BASE + 0x00201000;
