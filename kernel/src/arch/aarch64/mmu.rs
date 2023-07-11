use super::bsp::memory::{
    DEVICE_MEM_END, DEVICE_MEM_START, ROM_END, ROM_START, SRAM_END, SRAM_START,
};
use awkernel_aarch64::{
    dsb_ish, dsb_sy, get_current_el, id_aa64mmfr0_el1, isb, mair_el1, sctlr_el1, sctlr_el2,
    sctlr_el3, tcr_el1, ttbr0_el1, ttbr1_el1,
};
use awkernel_lib::{
    arch::aarch64::{
        page_allocator::PageAllocator,
        page_table::{flags, FrameAllocator, PageTable},
    },
    console::unsafe_puts,
    delay::wait_forever,
    memory::PAGESIZE,
};
use core::arch::asm;

const NUM_CPU: u64 = super::config::CORE_COUNT as u64;

pub const STACK_SIZE: u64 = 2 * 1024 * 1024; // 2MiB

static mut MEMORY_MAP: Addr = Addr {
    no_cache_start: 0,
    no_cache_end: 0,
    rom_start: 0,
    rom_end: 0,
    sram_start: 0,
    sram_end: 0,
    stack_size: 0,
    pager_mem_start: 0,
    pager_mem_end: 0,
    ttbr0: 0,
    ttbr1: 0,
};

extern "C" {
    static __kernel_start: u64;
    static __free_mem_start: u64;
    static __data_start: u64;
    static __data_end: u64;
    static __bss_start: u64;
    static __bss_end: u64;
    static __stack_el1_end: u64;
    static __stack_el1_start: u64;
}

pub fn get_free_mem_start() -> u64 {
    unsafe { &__free_mem_start as *const u64 as u64 }
}

pub fn get_ram_start() -> u64 {
    unsafe { &__kernel_start as *const u64 as u64 }
}

pub fn get_stack_el1_start() -> u64 {
    unsafe { &__stack_el1_start as *const u64 as u64 }
}

pub fn get_stack_el1_end() -> u64 {
    unsafe { &__stack_el1_end as *const u64 as u64 }
}

pub fn get_bss_start() -> u64 {
    unsafe { &__bss_start as *const u64 as u64 }
}

pub fn _get_bss_end() -> u64 {
    unsafe { &__bss_end as *const u64 as u64 }
}

pub fn get_data_start() -> u64 {
    unsafe { &__data_start as *const u64 as u64 }
}

pub fn _get_data_end() -> u64 {
    unsafe { &__data_end as *const u64 as u64 }
}

// logical address information
#[derive(Debug)]
pub struct Addr {
    // must be same as physical
    pub no_cache_start: u64,
    pub no_cache_end: u64,
    pub rom_start: u64,
    pub rom_end: u64,
    pub sram_start: u64,
    pub sram_end: u64,

    pub stack_size: u64,

    // free memory region for allocator
    pub pager_mem_start: u64,
    pub pager_mem_end: u64,

    // base address of page table
    pub ttbr0: u64,
    pub ttbr1: u64,
}

impl Addr {
    fn init(&mut self) {
        self.no_cache_start = get_free_mem_start();
        self.no_cache_end = self.no_cache_start + PAGESIZE as u64 * NUM_CPU;

        // free Memory region
        self.pager_mem_start = self.no_cache_end;
        self.pager_mem_end = self.pager_mem_start + 320 * 1024 * 1024; // 256 + 64MiB

        // 2MiB stack for each
        self.stack_size = STACK_SIZE;

        // ROM
        self.rom_start = ROM_START;
        self.rom_end = ROM_END;

        // SRAM
        self.sram_start = SRAM_START;
        self.sram_end = SRAM_END;
    }
}

pub fn init_memory_map() {
    unsafe {
        MEMORY_MAP.init();
    }
}

pub fn get_memory_map_mut() -> &'static mut Addr {
    unsafe {
        let addr = &mut MEMORY_MAP as *mut Addr as usize;
        (addr as *mut Addr).as_mut().unwrap()
    }
}

pub fn get_memory_map() -> &'static Addr {
    unsafe {
        let addr = &mut MEMORY_MAP as *mut Addr as usize;
        (addr as *mut Addr).as_mut().unwrap()
    }
}

pub fn _enabled() -> Option<bool> {
    let el = get_current_el();
    if el == 1 {
        let sctlr = sctlr_el1::get();
        Some(sctlr & 1 == 1)
    } else if el == 2 {
        let sctlr = sctlr_el2::get();
        Some(sctlr & 1 == 1)
    } else if el == 3 {
        let sctlr = sctlr_el3::get();
        Some((sctlr & 1) == 1)
    } else {
        None
    }
}

fn _get_sctlr() -> u64 {
    let el = get_current_el();
    if el == 1 {
        sctlr_el1::get()
    } else if el == 2 {
        sctlr_el2::get()
    } else if el == 3 {
        sctlr_el3::get()
    } else {
        0
    }
}

unsafe fn _set_sctlr(sctlr: u64) {
    let el = get_current_el();
    if el == 1 {
        sctlr_el1::set(sctlr);
    } else if el == 2 {
        sctlr_el2::set(sctlr);
    } else if el == 3 {
        sctlr_el3::set(sctlr);
    }
}

pub fn user_page_flag() -> u64 {
    use flags::*;
    FLAG_L3_XN | FLAG_L3_PXN | FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_RW_N | FLAG_L3_ATTR_MEM | 0b11
}

pub fn kernel_page_flag() -> u64 {
    use flags::*;
    FLAG_L3_XN | FLAG_L3_PXN | FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_RW_N | FLAG_L3_ATTR_MEM | 0b11
}

/// set registers
pub unsafe fn enable() {
    let addr = get_memory_map();
    assert!(addr.ttbr0 != 0 && addr.ttbr1 != 0);

    set_reg_el1(addr.ttbr0 as usize, addr.ttbr1 as usize);
    init_sp_el1();
}

/// initialize transition tables
pub fn init() -> Option<(PageTable, PageTable)> {
    let addr = get_memory_map_mut();

    // check for 4KiB granule and at least 36 bits physical address bus
    let mmfr = id_aa64mmfr0_el1::get();
    let b = mmfr & 0xF;
    if b < 1
    /* 36 bits */
    {
        unsafe { unsafe_puts("ERROR: 36 bit address space not supported.\n") };
        return None;
    }

    if mmfr & (0xF << 28) != 0
    /* 4KiB */
    {
        unsafe { unsafe_puts("4KiB granule not support.\n") };
        return None;
    }

    init_sp_el1(); // stack pointer

    Some(init_el1(addr))
}

fn get_mair() -> u64 {
    0xFF         | // AttrIdx=0: normal, IWBWA, OWBWA, NTR
    (0x04 <<  8) | // AttrIdx=1: device, nGnRE (must be OSH too)
    (0x44 << 16) // AttrIdx=2: non cacheable
}

/// for TCR_EL2 and TCR_EL2
fn _get_tcr() -> u64 {
    let mmfr = id_aa64mmfr0_el1::get();
    let b = mmfr & 0xF;

    1 << 31 | // Res1
    1 << 23 | // Res1
    b << 16 |
    1 << 14 | // 64KiB granule
    3 << 12 | // inner shadable
    1 << 10 | // Normal memory, Outer Write-Back Read-Allocate Write-Allocate Cacheable.
    1 <<  8 | // Normal memory, Inner Write-Back Read-Allocate Write-Allocate Cacheable.
    22 // T0SZ = 22, 2 levels (level 2 and 3 translation tables), 2^42B (4TiB) space
}

fn update_sctlr(sctlr: u64) -> u64 {
    let sctlr = sctlr   |
        1 << 44 | // set DSSBS, enable speculative load and store
        1 << 12 | // set I, instruction cache
        1 <<  2 | // set C, data cache
        1; // set M, enable MMU
    sctlr
        & !(
            1 << 25 | // clear EE
        1 << 19 | // clear WXN
        1 <<  3 | // clear SA
        1 <<  1
            // clear A
        )
}

/// set up EL1's page table
/// assume 2MiB stack space per CPU
fn init_el1(addr: &mut Addr) -> (PageTable, PageTable) {
    use flags::*;

    // init the page allocator
    let start = addr.pager_mem_start;
    let end = addr.pager_mem_end;
    let mut allocator = PageAllocator::new(start, end);

    //-------------------------------------------------------------------------
    // TTBR0: Kernel Space
    let mut table0 = PageTable::new(&mut allocator);

    // map .init and .text section
    let mut ram_start = get_ram_start();
    let data_start = get_data_start();
    let flag = FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_R_N | FLAG_L3_ATTR_MEM | 0b11;
    while ram_start < data_start {
        table0.map_to(ram_start, ram_start, flag, &mut allocator);
        ram_start += PAGESIZE as u64;
    }

    // map .data
    let mut data_start = get_data_start();
    let bss_start = get_bss_start();
    let flag = FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_MEM
        | 0b11;
    while data_start < bss_start {
        table0.map_to(data_start, data_start, flag, &mut allocator);
        data_start += PAGESIZE as u64;
    }

    // map .bss section
    let mut bss_start = get_bss_start();
    let end = get_stack_el1_end();
    let flag = FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_MEM
        | 0b11;
    while bss_start < end {
        table0.map_to(bss_start, bss_start, flag, &mut allocator);
        bss_start += PAGESIZE as u64;
    }

    // map stack memory
    let mut stack_end = get_stack_el1_end();
    let stack_start = get_stack_el1_start();
    let flag = kernel_page_flag();
    let start = stack_end;
    while stack_end < stack_start {
        if (stack_end - start) & (addr.stack_size - 1) != 0 {
            table0.map_to(stack_end, stack_end, flag, &mut allocator);
        }
        stack_end += PAGESIZE as u64;
    }

    // map device memory
    let mut device_addr = DEVICE_MEM_START;
    let flag = FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_OSH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_DEV
        | 0b11;
    while device_addr < DEVICE_MEM_END {
        table0.map_to(device_addr, device_addr, flag, &mut allocator);
        device_addr += PAGESIZE as u64;
    }

    // map pager memory
    let mut pager_start = addr.pager_mem_start;
    let flag = FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_NC
        | 0b11;
    while pager_start < addr.pager_mem_end {
        table0.map_to(pager_start, pager_start, flag, &mut allocator);
        pager_start += PAGESIZE as u64;
    }

    // map heap memory
    let mut vm_addr = crate::config::HEAP_START;
    let flag = user_page_flag();
    while vm_addr
        < super::config::HEAP_START + crate::config::HEAP_SIZE + crate::config::BACKUP_HEAP_SIZE
    {
        let phy_addr = if let Some(addr) = allocator.allocate_frame() {
            addr
        } else {
            unsafe { unsafe_puts("failed to allocate page.\n") };
            wait_forever();
        };
        table0.map_to(vm_addr, phy_addr, flag, &mut allocator);
        vm_addr += PAGESIZE as u64;
    }

    //-------------------------------------------------------------------------
    // TTBR1: user space
    let table1 = PageTable::new(&mut allocator);

    addr.ttbr0 = table0.addr();
    addr.ttbr1 = table1.addr();

    (table0, table1)
}

unsafe fn set_reg_el1(ttbr0: usize, ttbr1: usize) {
    // first, set Memory Attributes array, indexed by PT_MEM, PT_DEV, PT_NC
    mair_el1::set(get_mair());

    let mmfr = id_aa64mmfr0_el1::get();
    let b = mmfr & 0xF;

    let tcr: u64 = b << 32 |
         0b10 << 30 | // 4KiB granule, TTBR1_EL1
         3 << 28 | // inner shadable, TTBR1_EL1
         2 << 26 | // Normal memory, Outer Write-Through Read-Allocate Write-Allocate Cacheable, TTBR1_EL1
         1 << 24 | // Normal memory, Inner Write-Back Read-Allocate Write-Allocate Cacheable, TTBR1_EL1
        25 << 16 | // T1SZ = 25, 3 levels (level 1,  2 and 3 translation tables), 2^39B (512GiB) space
         // 0b00 << 14 | // 4KiB granule
         3 << 12 | // inner shadable, TTBR0_EL1
         2 << 10 | // Normal memory, Outer Write-Through Read-Allocate Write-Allocate Cacheable, TTBR0_EL1
         1 <<  8 | // Normal memory, Inner Write-Back Read-Allocate Write-Allocate Cacheable, TTBR0_EL1
        25; // T0SZ = 25,  3 levels (level 1,  2 and 3 translation tables), 2^39B (512GiB) space

    // next, specify mapping characteristics in translate control register
    tcr_el1::set(tcr);

    // tell the MMU where our translation tables are.
    ttbr0_el1::set(ttbr0 as u64 | 1);
    ttbr1_el1::set(ttbr1 as u64 | 1);

    // finally, toggle some bits in system control register to enable page translation
    dsb_ish();
    isb();

    let sctlr = sctlr_el1::get();
    let sctlr = update_sctlr(sctlr) & !(1 << 4); // clear SA0

    sctlr_el1::set(sctlr);
    dsb_sy();
    isb();
}

pub fn _get_no_cache<T>() -> &'static mut T {
    let addr = get_memory_map();
    let addr = addr.no_cache_start + PAGESIZE as u64 * super::cpu::core_pos() as u64;
    unsafe {
        let addr = addr as *mut u64 as usize;
        (addr as *mut T).as_mut().unwrap()
    }
}

pub fn _tlb_flush_all() {
    unsafe {
        asm!(
            "dsb ishst
             tlbi vmalle1is
             dsb ish
             isb",
        )
    };
}

pub fn _tlb_flush_addr(vm_addr: usize) {
    unsafe {
        asm!(
            "dsb ishst
             tlbi vaae1is, {}
             dsb ish
             isb",
             in(reg) (vm_addr >> 12) & !0b1111
        )
    };
}

#[allow(unused_assignments)]
fn init_sp_el1() {
    let mut sp = 0;
    unsafe {
        asm!(
            "
        mov {0:x}, sp
        msr spsel, #1
        mov sp, {0:x}",
            inout(reg) sp
        )
    };
}
