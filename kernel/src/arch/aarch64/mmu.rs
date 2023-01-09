use core::{
    arch::asm,
    ptr::{read_volatile, write_volatile},
    slice,
};

use super::bsp::memory::{
    DEVICE_MEM_END, DEVICE_MEM_START, ROM_END, ROM_START, SRAM_END, SRAM_START,
};
use super::cpu;

const NUM_CPU: u64 = super::config::CORE_COUNT as u64;

pub const EL1_ADDR_OFFSET: u64 = 0x3FFFFF << 42;

// level 2 table x 1 (for 4TiB space)
// level 3 table x 8 (for 512MiB x 8 = 4GiB space)
// level 3 table x 32 (for 512MiB x 32 = 16GiB space, 64MiB * 256 Processes = 16GiB)
pub const KERN_TTBR0_LV2_TABLE_NUM: usize = 1;
pub const KERN_TTBR0_LV3_TABLE_NUM1: usize = 8; // from 0B to 4GiB
pub const KERN_TTBR0_LV3_TABLE_NUM2: usize = 32; // from 1TiB to 1TiB + 16GiB
pub const KERN_TTBR0_TABLE_NUM: usize =
    KERN_TTBR0_LV2_TABLE_NUM + KERN_TTBR0_LV3_TABLE_NUM1 + KERN_TTBR0_LV3_TABLE_NUM2;

// level 2 table x 1 (for 4TiB space)
// level 3 table x 4 (for 512MiB x 4 = 2GiB space)
pub const KERN_TTBR1_LV2_TABLE_NUM: usize = 1;
pub const KERN_TTBR1_LV3_TABLE_NUM: usize = 4;
pub const KERN_TTBR1_TABLE_NUM: usize = KERN_TTBR1_LV2_TABLE_NUM + KERN_TTBR1_LV3_TABLE_NUM;

pub const STACK_SIZE: u64 = 32 * PAGESIZE; // 2MiB

static mut MEMORY_MAP: Addr = Addr {
    no_cache_start: 0,
    no_cache_end: 0,
    tt_el1_ttbr0_start: 0,
    tt_el1_ttbr0_end: 0,
    tt_el1_ttbr1_start: 0,
    tt_el1_ttbr1_end: 0,
    rom_start: 0,
    rom_end: 0,
    sram_start: 0,
    sram_end: 0,
    stack_size: 0,
    pager_mem_start: 0,
    pager_mem_end: 0,
};

extern "C" {
    static __ram_start: u64;
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
    unsafe { &__ram_start as *const u64 as u64 }
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

pub fn get_bss_end() -> u64 {
    unsafe { &__bss_end as *const u64 as u64 }
}

pub fn get_data_start() -> u64 {
    unsafe { &__data_start as *const u64 as u64 }
}

pub fn get_data_end() -> u64 {
    unsafe { &__data_end as *const u64 as u64 }
}

// 64KB page
// level 2 and 3 translation tables

pub const PAGESIZE: u64 = 64 * 1024;

// NSTable (63bit)
const FLAG_L2_NS: u64 = 1 << 63; // non secure table

const FLAG_L3_XN: u64 = 1 << 54; // execute never
const FLAG_L3_PXN: u64 = 1 << 53; // priviledged execute
const FLAG_L3_CONT: u64 = 1 << 52; // contiguous
const FLAG_L3_DBM: u64 = 1 << 51; // dirty bit modifier
const FLAG_L3_AF: u64 = 1 << 10; // access flag
const FLAG_L3_NS: u64 = 1 << 5; // non secure

const OFFSET_USER_HEAP_PAGE: usize = 2048; // 1TiB offset

// [9:8]: Shareability attribute, for Normal memory
//    | Shareability
// ---|------------------
// 00 | non sharedable
// 01 | reserved
// 10 | outer sharedable
// 11 | inner sharedable
const FLAG_L3_OSH: u64 = 0b10 << 8;
const FLAG_L3_ISH: u64 = 0b11 << 8;

// [7:6]: access permissions
//    | Access from            |
//    | higher Exception level | Access from EL0
// ---|------------------------|-----------------
// 00 | read/write             | none
// 01 | read/write             | read/write
// 10 | read-only              | none
// 11 | read-only              | read-only
const FLAG_L3_SH_RW_N: u64 = 0;
const FLAG_L3_SH_RW_RW: u64 = 1 << 6;
const FLAG_L3_SH_R_N: u64 = 0b10 << 6;
const FLAG_L3_SH_R_R: u64 = 0b11 << 6;

// [4:2]: AttrIndx
// defined in MAIR register
// see get_mair()
const FLAG_L3_ATTR_MEM: u64 = 0; // normal memory
const FLAG_L3_ATTR_DEV: u64 = 1 << 2; // device MMIO
const FLAG_L3_ATTR_NC: u64 = 2 << 2; // non-cachable

// transition table
pub struct TTable {
    tt_lv2: &'static mut [u64],
    tt_lv3_1: &'static mut [u64],
    tt_lv3_2: &'static mut [u64],
    num_lv2: usize,
    num_lv3_1: usize,
    num_lv3_2: usize,
}

// logical address information
#[derive(Debug)]
pub struct Addr {
    // must be same as physical
    pub no_cache_start: u64,
    pub no_cache_end: u64,
    pub tt_el1_ttbr0_start: u64,
    pub tt_el1_ttbr0_end: u64,
    pub tt_el1_ttbr1_start: u64,
    pub tt_el1_ttbr1_end: u64,
    pub rom_start: u64,
    pub rom_end: u64,
    pub sram_start: u64,
    pub sram_end: u64,

    pub stack_size: u64,

    // independent from physical
    pub pager_mem_start: u64,
    pub pager_mem_end: u64,
}

impl Addr {
    fn init(&mut self) {
        self.no_cache_start = get_free_mem_start();
        self.no_cache_end = self.no_cache_start + PAGESIZE * NUM_CPU;

        // MMU's transition table #0 for EL1
        self.tt_el1_ttbr0_start = self.no_cache_end;
        self.tt_el1_ttbr0_end = self.tt_el1_ttbr0_start + PAGESIZE * KERN_TTBR0_TABLE_NUM as u64;

        // MMU's transition table #1 for EL1
        // level 2 table x 1 (for 4TiB space)
        // level 3 table x 1 (for 512MiB space)
        self.tt_el1_ttbr1_start = self.tt_el1_ttbr0_end;
        self.tt_el1_ttbr1_end = self.tt_el1_ttbr1_start + PAGESIZE * KERN_TTBR1_TABLE_NUM as u64;

        // 2MiB stack for each
        self.stack_size = STACK_SIZE;

        // heap memory
        self.pager_mem_start = self.tt_el1_ttbr1_end;
        self.pager_mem_end = self.pager_mem_start + 64 * 1024 * 1024; // 64MiB

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

pub fn get_memory_map() -> &'static Addr {
    unsafe {
        let addr = &mut MEMORY_MAP as *mut Addr as usize;
        (addr as *mut Addr).as_mut().unwrap()
    }
}

pub fn get_ttbr0() -> TTable {
    let addr = get_memory_map();
    TTable::new(
        addr.tt_el1_ttbr0_start + EL1_ADDR_OFFSET,
        KERN_TTBR0_LV2_TABLE_NUM,
        KERN_TTBR0_LV3_TABLE_NUM1,
        KERN_TTBR0_LV3_TABLE_NUM2,
    )
}

pub fn get_ttbr1() -> TTable {
    let addr = get_memory_map();
    TTable::new(
        addr.tt_el1_ttbr1_start + EL1_ADDR_OFFSET,
        KERN_TTBR1_LV2_TABLE_NUM,
        KERN_TTBR1_LV3_TABLE_NUM,
        0,
    )
}

impl TTable {
    fn new(tt_addr: u64, num_lv2: usize, num_lv3_1: usize, num_lv3_2: usize) -> TTable {
        let ptr = tt_addr as *mut u64;
        let tt_lv2 = unsafe { slice::from_raw_parts_mut(ptr, 8192 * num_lv2) };

        // 0... space
        let ptr = ((PAGESIZE * num_lv2 as u64) + tt_addr) as *mut u64;
        let tt_lv3_1 = unsafe { slice::from_raw_parts_mut(ptr, 8192 * num_lv3_1) };

        // 1TiB... space
        let ptr = ((PAGESIZE * (num_lv2 + num_lv3_1) as u64) + tt_addr) as *mut u64;
        let tt_lv3_2 = unsafe { slice::from_raw_parts_mut(ptr, 8192 * num_lv3_2) };

        TTable {
            tt_lv2,
            tt_lv3_1,
            tt_lv3_2,
            num_lv2,
            num_lv3_1,
            num_lv3_2,
        }
    }

    fn init(&mut self) {
        // zero clear
        for e in self.tt_lv2.iter_mut() {
            *e = 0;
        }

        for e in self.tt_lv3_1.iter_mut() {
            *e = 0;
        }

        for e in self.tt_lv3_2.iter_mut() {
            *e = 0;
        }

        // set up level 2 tables for 0... space
        for i in 0..(8192 * self.num_lv2) {
            if i >= self.num_lv3_1 {
                break;
            }
            self.tt_lv2[i] = (&self.tt_lv3_1[i * 8192] as *const u64) as u64 | 0b11;
        }

        // set up level 2 tables for 1TiB... space
        for i in OFFSET_USER_HEAP_PAGE..(8192 * self.num_lv2) {
            let idx = i - OFFSET_USER_HEAP_PAGE;
            if idx >= self.num_lv3_2 {
                break;
            }
            self.tt_lv2[i] = (&self.tt_lv3_2[idx * 8192] as *const u64) as u64 | 0b11;
        }
    }

    pub fn map(&mut self, vm_addr: u64, phy_addr: u64, flag: u64) {
        let lv2idx = ((vm_addr >> 29) & 8191) as usize;
        let lv3idx = ((vm_addr >> 16) & 8191) as usize;

        if lv2idx >= (self.num_lv2 * 8192) {
            // memory access error
            panic!("memory map error");
        }

        let e = phy_addr & !0xffff | flag;

        if lv2idx < OFFSET_USER_HEAP_PAGE {
            let idx = lv2idx * 8192 + lv3idx;
            unsafe { write_volatile(&mut self.tt_lv3_1[idx], e) };
        } else {
            let idx = (lv2idx - OFFSET_USER_HEAP_PAGE) * 8192 + lv3idx;
            unsafe { write_volatile(&mut self.tt_lv3_2[idx], e) };
        }
    }

    pub fn unmap(&mut self, vm_addr: u64) {
        let lv2idx = ((vm_addr >> 29) & 8191) as usize;
        let lv3idx = ((vm_addr >> 16) & 8191) as usize;

        if lv2idx >= (self.num_lv2 * 8192) {
            // memory access error
            panic!("memory unmap error");
        }

        if lv2idx < OFFSET_USER_HEAP_PAGE {
            let idx = lv2idx * 8192 + lv3idx;
            unsafe { write_volatile(&mut self.tt_lv3_1[idx], 0) };
        } else {
            let idx = (lv2idx - OFFSET_USER_HEAP_PAGE) * 8192 + lv3idx;
            unsafe { write_volatile(&mut self.tt_lv3_2[idx], 0) };
        }
    }

    pub fn to_phy_addr(&self, vm_addr: u64) -> Option<u64> {
        let lv2idx = ((vm_addr >> 29) & 8191) as usize;
        let lv3idx = ((vm_addr >> 16) & 8191) as usize;

        let val = if lv2idx < OFFSET_USER_HEAP_PAGE {
            let idx = lv2idx * 8192 + lv3idx;
            unsafe { read_volatile(&self.tt_lv3_1[idx]) }
        } else {
            let idx = (lv2idx - OFFSET_USER_HEAP_PAGE) * 8192 + lv3idx;
            unsafe { read_volatile(&self.tt_lv3_2[idx]) }
        };

        if val == 0 {
            return None;
        }

        let high = (val >> 32) & 0xffff;
        let mid = (val >> 16) & 0xffff;
        let low = vm_addr & 0xffff;

        Some((high << 32) | (mid << 16) | low)
    }
}

pub fn enabled() -> Option<bool> {
    let el = cpu::get_current_el();
    if el == 1 {
        let sctlr = cpu::sctlr_el1::get();
        Some(sctlr & 1 == 1)
    } else if el == 2 {
        let sctlr = cpu::sctlr_el2::get();
        Some(sctlr & 1 == 1)
    } else if el == 3 {
        let sctlr = cpu::sctlr_el3::get();
        Some((sctlr & 1) == 1)
    } else {
        None
    }
}

fn get_sctlr() -> u64 {
    let el = cpu::get_current_el();
    if el == 1 {
        cpu::sctlr_el1::get()
    } else if el == 2 {
        cpu::sctlr_el2::get()
    } else if el == 3 {
        cpu::sctlr_el3::get()
    } else {
        0
    }
}

fn set_sctlr(sctlr: u64) {
    let el = cpu::get_current_el();
    if el == 1 {
        cpu::sctlr_el1::set(sctlr);
    } else if el == 2 {
        cpu::sctlr_el2::set(sctlr);
    } else if el == 3 {
        cpu::sctlr_el3::set(sctlr);
    }
}

pub fn user_page_flag() -> u64 {
    FLAG_L3_XN | FLAG_L3_PXN | FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_RW_RW | FLAG_L3_ATTR_MEM | 0b11
}

pub fn kernel_page_flag() -> u64 {
    FLAG_L3_XN | FLAG_L3_PXN | FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_RW_N | FLAG_L3_ATTR_MEM | 0b11
}

/// set registers
pub fn enable() {
    let addr = get_memory_map();

    set_reg_el1(
        addr.tt_el1_ttbr0_start as usize,
        addr.tt_el1_ttbr1_start as usize,
    );
}

/// initialize transition tables
pub fn init() -> Option<(TTable, TTable)> {
    let addr = get_memory_map();

    // addr.print();

    // check for 64KiB granule and at least 36 bits physical address bus
    let mmfr = cpu::id_aa64mmfr0_el1::get();
    let b = mmfr & 0xF;
    if b < 1
    /* 36 bits */
    {
        // driver::uart::puts("ERROR: 36 bit address space not supported\n");
        return None;
    }

    if mmfr & (0xF << 24) != 0
    /* 64KiB */
    {
        // driver::uart::puts("ERROR: 64KiB granule not supported\n");
        return None;
    }

    init_sp_el1();

    Some(init_el1(&addr))
}

fn get_mair() -> u64 {
    (0xFF <<  0) | // AttrIdx=0: normal, IWBWA, OWBWA, NTR
    (0x04 <<  8) | // AttrIdx=1: device, nGnRE (must be OSH too)
    (0x44 << 16) // AttrIdx=2: non cacheable
}

/// for TCR_EL2 and TCR_EL2
fn get_tcr() -> u64 {
    let mmfr = cpu::id_aa64mmfr0_el1::get();
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

/// set up EL1's page table, 64KB page, level 2 and 3 translation tables,
/// assume 2MiB stack space per CPU
fn init_el1(addr: &Addr) -> (TTable, TTable) {
    // TTBR0: kernel and user space
    let mut table0 = TTable::new(
        addr.tt_el1_ttbr0_start,
        KERN_TTBR0_LV2_TABLE_NUM,
        KERN_TTBR0_LV3_TABLE_NUM1,
        KERN_TTBR0_LV3_TABLE_NUM2,
    );

    table0.init();

    // map .init and .text section
    let mut ram_start = get_ram_start();
    let data_start = get_data_start();
    let flag = FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_R_R | FLAG_L3_ATTR_MEM | 0b11;
    while ram_start < data_start {
        table0.map(ram_start, ram_start, flag);
        ram_start += PAGESIZE;
    }

    // map .data
    let mut data_start = get_data_start();
    let bss_start = get_bss_start();
    let flag = FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_RW
        | FLAG_L3_ATTR_MEM
        | 0b11;
    while data_start < bss_start {
        table0.map(data_start, data_start, flag);
        data_start += PAGESIZE;
    }

    // map .bss section
    let mut bss_start = get_bss_start();
    let end = get_stack_el1_end();
    let flag = FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_RW
        | FLAG_L3_ATTR_MEM
        | 0b11;
    while bss_start < end {
        table0.map(bss_start, bss_start, flag);
        bss_start += PAGESIZE;
    }

    // map stack memory
    let mut stack_end = get_stack_el1_end();
    let stack_start = get_stack_el1_start();
    let flag = kernel_page_flag();
    while stack_end < stack_start {
        table0.map(stack_end, stack_end, flag);
        stack_end += PAGESIZE;
    }

    for i in 0..NUM_CPU {
        let addr = stack_end + i * addr.stack_size;
        table0.unmap(addr);
    }

    // map heap memory
    let mut heap_start = addr.pager_mem_start;
    let mut vm_addr = crate::config::HEAP_START;
    let flag = kernel_page_flag();
    while heap_start < addr.pager_mem_end {
        table0.map(vm_addr, heap_start, flag);
        heap_start += PAGESIZE;
        vm_addr += PAGESIZE;
    }

    // map device memory
    let mut device_addr = DEVICE_MEM_START;
    let flag = FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_OSH
        | FLAG_L3_SH_RW_RW
        | FLAG_L3_ATTR_DEV
        | 0b11;
    while device_addr < DEVICE_MEM_END {
        table0.map(device_addr, device_addr, flag);
        device_addr += PAGESIZE;
    }

    //-------------------------------------------------------------------------
    // TTBR1: kernel space
    let mut table1 = TTable::new(
        addr.tt_el1_ttbr1_start,
        KERN_TTBR1_LV2_TABLE_NUM,
        KERN_TTBR1_LV3_TABLE_NUM,
        0,
    );

    table1.init();

    // map transition table for TTBR0
    let mut tt_start = addr.tt_el1_ttbr0_start;
    let flag = FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_OSH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_DEV
        | 0b11;
    while tt_start < addr.tt_el1_ttbr0_end {
        table1.map(tt_start, tt_start, flag);
        tt_start += PAGESIZE;
    }

    // map transition table for TTBR1
    let mut tt_start = addr.tt_el1_ttbr1_start;
    let flag = FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_OSH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_DEV
        | 0b11;
    while tt_start < addr.tt_el1_ttbr1_end {
        table1.map(tt_start, tt_start, flag);
        tt_start += PAGESIZE;
    }

    (table0, table1)
}

fn set_reg_el1(ttbr0: usize, ttbr1: usize) {
    // first, set Memory Attributes array, indexed by PT_MEM, PT_DEV, PT_NC in our example
    cpu::mair_el1::set(get_mair());

    let mmfr = cpu::id_aa64mmfr0_el1::get();
    let b = mmfr & 0xF;

    let tcr: u64 = b << 32 |
         3 << 30 | // 64KiB granule, TTBR1_EL1
         3 << 28 | // inner shadable, TTBR1_EL1
         2 << 26 | // Normal memory, Outer Write-Through Read-Allocate Write-Allocate Cacheable, TTBR1_EL1
         1 << 24 | // Normal memory, Inner Write-Back Read-Allocate Write-Allocate Cacheable, TTBR1_EL1
        22 << 16 | // T1SZ = 22, 2 levels (level 2 and 3 translation tables), 2^42B (4TiB) space
         1 << 14 | // 64KiB granule
         3 << 12 | // inner shadable, TTBR0_EL1
         2 << 10 | // Normal memory, Outer Write-Through Read-Allocate Write-Allocate Cacheable, TTBR0_EL1
         1 <<  8 | // Normal memory, Inner Write-Back Read-Allocate Write-Allocate Cacheable, TTBR0_EL1
        22; // T0SZ = 22, 2 levels (level 2 and 3 translation tables), 2^42B (4TiB) space

    // next, specify mapping characteristics in translate control register
    cpu::tcr_el1::set(tcr);

    // tell the MMU where our translation tables are.
    cpu::ttbr0_el1::set(ttbr0 as u64 | 1);
    cpu::ttbr1_el1::set(ttbr1 as u64 | 1);

    // finally, toggle some bits in system control register to enable page translation
    cpu::dsb_ish();
    cpu::isb();

    let sctlr = cpu::sctlr_el1::get();
    let sctlr = update_sctlr(sctlr) & !(1 << 4); // clear SA0

    cpu::sctlr_el1::set(sctlr);
    cpu::dsb_sy();
    cpu::isb();
}

pub fn get_no_cache<T>() -> &'static mut T {
    let addr = get_memory_map();
    let addr = addr.no_cache_start + PAGESIZE * super::cpu::core_pos() as u64;
    unsafe {
        let addr = addr as *mut u64 as usize;
        (addr as *mut T).as_mut().unwrap()
    }
}

pub fn tlb_flush_all() {
    unsafe {
        asm!(
            "dsb ishst
             tlbi vmalle1is
             dsb ish
             isb",
        )
    };
}

pub fn tlb_flush_addr(vm_addr: usize) {
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

fn init_sp_el1() {
    let stack = get_stack_el1_start();
    for i in 0..NUM_CPU {
        let addr = stack - (i as u64) * STACK_SIZE + EL1_ADDR_OFFSET;
        unsafe {
            asm!(
                "msr spsel, #1
                 mov sp, {}
                 msr spsel, #0",
                in(reg) addr
            );
        }
    }
}
