use crate::arch::config::HEAP_START;
use awkernel_aarch64::{
    dsb_ish, dsb_sy, id_aa64mmfr0_el1, isb, mair_el1, sctlr_el1, tcr_el1, ttbr0_el1,
};
use awkernel_lib::{
    arch::aarch64::{
        page_allocator::PageAllocator,
        page_table::{
            flags::{self, FLAG_L3_CONT},
            FrameAllocator, PageTable,
        },
    },
    console::{unsafe_print_hex_u32, unsafe_print_hex_u64, unsafe_puts},
    device_tree::{node::DeviceTreeNode, prop::PropertyValue},
    err_msg,
    memory::PAGESIZE,
};
use core::{alloc::Allocator, arch::asm};

pub const STACK_SIZE: usize = 2 * 1024 * 1024; // 2MiB

extern "C" {
    static __kernel_start: u64;
    static __data_start: u64;
    static __stack_memory: u64;
}

pub fn get_kernel_start() -> u64 {
    unsafe { &__kernel_start as *const u64 as u64 }
}

pub fn get_data_start() -> u64 {
    unsafe { &__data_start as *const u64 as u64 }
}

pub fn get_stack_memory() -> u64 {
    unsafe { &__stack_memory as *const u64 as u64 }
}

#[derive(Debug, Clone, Copy)]
pub struct MemoryRange {
    start: usize,
    end: usize,
}

#[derive(Debug, Clone, Copy)]
enum ContainResult {
    Contain,
    NotContain,
    Overlap,
}

impl MemoryRange {
    /// ---: start-to-end
    /// ***: unused
    ///
    /// If
    /// - self:  `****----------****`
    /// - range: `******-----*******`
    /// then, `ContainResult::Contain` will be returned.
    ///
    /// If
    /// - self:  `*********------***`
    /// - range: `**-----***********`
    /// then, `ContainResult::NotContain` will be returned.
    ///
    /// If
    /// - self:  `****----------****`
    /// - range: `**--------********`
    /// then, `ContainResult::Overlap` will be returned.
    fn contains(&self, range: MemoryRange) -> ContainResult {
        if self.start <= range.start && range.end <= self.end {
            ContainResult::Contain
        } else if range.end <= self.start || self.end <= range.start {
            ContainResult::NotContain
        } else {
            ContainResult::Overlap
        }
    }
}

const NUM_RANGES: usize = 16;

pub struct VM {
    num_cpus: usize,

    idx_dev: usize,
    device_ranges: [Option<MemoryRange>; NUM_RANGES],

    idx_heap: usize,
    heap: [Option<MemoryRange>; NUM_RANGES], // RW and used by the page table.

    idx_ro: usize,
    ro_ranges: [Option<MemoryRange>; NUM_RANGES],

    table0: Option<PageTable>,
    heap_size: Option<usize>,
}

pub fn kernel_page_flag_rw() -> u64 {
    use flags::*;
    FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_MEM
        | 0b11
}

pub fn kernel_page_flag_ro() -> u64 {
    use flags::*;
    FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_R_N
        | FLAG_L3_ATTR_MEM
        | 0b11
}

pub fn kernel_page_flag_r_exec() -> u64 {
    use flags::*;
    FLAG_L3_NS | FLAG_L3_XN | FLAG_L3_AF | FLAG_L3_ISH | FLAG_L3_SH_R_N | FLAG_L3_ATTR_MEM | 0b11
}

pub fn kernel_page_flag_rw_no_cache() -> u64 {
    use flags::*;
    FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_ISH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_MEM
        | FLAG_L3_ATTR_NC
        | 0b11
}

pub fn device_page_flag() -> u64 {
    use flags::*;
    FLAG_L3_NS
        | FLAG_L3_XN
        | FLAG_L3_PXN
        | FLAG_L3_AF
        | FLAG_L3_OSH
        | FLAG_L3_SH_RW_N
        | FLAG_L3_ATTR_DEV
        | 0b11
}

impl VM {
    pub fn new() -> Self {
        VM {
            num_cpus: 0,
            idx_dev: 0,
            device_ranges: [None; NUM_RANGES],
            idx_heap: 0,
            heap: [None; NUM_RANGES],
            idx_ro: 0,
            ro_ranges: [None; NUM_RANGES],
            table0: None,
            heap_size: None,
        }
    }

    pub fn set_num_cpus(&mut self, num_cpus: usize) {
        self.num_cpus = num_cpus;
    }

    pub fn push_device_range(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if self.idx_dev >= self.device_ranges.len() {
            return Err(err_msg!("too many device range"));
        }

        self.device_ranges[self.idx_dev] = Some(MemoryRange { start, end });
        self.idx_dev += 1;

        Ok(())
    }

    /// Push a physical address region for heap memory.
    pub fn push_heap(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if start >= end {
            return Err(err_msg!("start >= end"));
        }

        if self.idx_heap >= self.heap.len() {
            return Err(err_msg!("too many device range"));
        }

        self.heap[self.idx_heap] = Some(MemoryRange { start, end });
        self.idx_heap += 1;

        Ok(())
    }

    /// Push a physical address region for Read-only memory.
    pub fn push_ro_memory(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if start >= end {
            return Err(err_msg!("start >= end"));
        }

        if self.idx_ro >= self.ro_ranges.len() {
            return Err(err_msg!("too many device range"));
        }

        self.ro_ranges[self.idx_ro] = Some(MemoryRange { start, end });
        self.idx_ro += 1;

        Ok(())
    }

    pub fn get_heap_size(&self) -> Option<usize> {
        self.heap_size
    }

    pub fn get_ttbr0_addr(&self) -> Option<usize> {
        let addr = self.table0.as_ref()?.addr();
        Some(addr as usize)
    }

    /// If
    /// - heap:   `***---------***`
    /// - remove: `*****---*******`
    /// then the heap will be `***--***----***`.
    pub fn remove_heap(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if start >= end {
            return Err(err_msg!("start >= end"));
        }

        let rm_range = MemoryRange { start, end };
        let mut idx = 0;
        let mut ranges = [None; NUM_RANGES];

        for range in self.heap.iter_mut() {
            if let Some(r) = range {
                match r.contains(rm_range) {
                    ContainResult::Contain => {
                        if r.end != rm_range.end {
                            ranges[idx] = Some(MemoryRange {
                                start: rm_range.end,
                                end: r.end,
                            });

                            idx += 1;
                        }

                        if r.start == rm_range.start {
                            *range = None;
                        } else {
                            r.end = rm_range.start;
                        }
                    }
                    ContainResult::Overlap => return Err(err_msg!("overlap")),
                    ContainResult::NotContain => (),
                }
            }
        }

        for range in ranges {
            if let Some(r) = range {
                self.push_heap(r.start, r.end)?;
            }
        }

        Ok(())
    }

    pub fn remove_kernel_memory_from_heap_memory(&mut self) -> Result<(), &'static str> {
        if self.num_cpus == 0 {
            return Err(err_msg!("num_cpus == 0"));
        }

        let start = get_kernel_start() as usize;
        let end = get_stack_memory() as usize + STACK_SIZE * self.num_cpus;

        self.remove_heap(start, end)
    }

    /// `add_heap_from_node` is a function to add heap memory regions from a device tree node.
    /// Specifically, this function looks for nodes whose names start with "memory@"
    /// and adds their memory regions to the heap.
    ///
    /// # Arguments
    ///
    /// * `device_tree_node`: This is a reference to a device tree node object.
    ///   It contains information about a specific device node in a device tree.
    ///
    /// # Returns
    ///
    /// * `Result`: This function returns `Result<(), &'static str>`.
    ///   If it is successful in adding memory, it returns `Ok(())`,
    ///   and if it fails, it returns `Err` with a static string explaining the error.
    pub fn add_heap_from_node<'a, A: Allocator + Clone>(
        &mut self,
        device_tree_node: &DeviceTreeNode<'a, A>,
    ) -> Result<(), &'static str> {
        // Add heap memory regions.
        for node in device_tree_node.nodes().iter() {
            if node.name().starts_with("memory@") {
                if let Some(reg_prop) = node.get_property("reg") {
                    match reg_prop.value() {
                        PropertyValue::Address(addr, len) => {
                            let start = addr.to_u128() as usize;
                            let end = start + len.to_u128() as usize;
                            self.push_heap(start, end)?;
                        }
                        PropertyValue::Addresses(addrs) => {
                            for (addr, len) in addrs {
                                let start = addr.to_u128() as usize;
                                let end = start + len.to_u128() as usize;
                                self.push_heap(start, end)?;
                            }
                        }
                        _ => (),
                    }
                }
            }
        }

        Ok(())
    }

    unsafe fn init_memory_map(&mut self) -> Option<()> {
        let mut allocator = PageAllocator::new();
        for mem in self.heap.iter() {
            if let Some(m) = mem {
                let _ = allocator.push(m.start as u64, m.end as u64);
            }
        }

        let mut table0 = PageTable::new(&mut allocator)?;

        // TEXT.
        let start = get_kernel_start();
        let end = get_data_start();
        let flag = kernel_page_flag_r_exec()
            | if (end - start) / PAGESIZE as u64 > 1 {
                FLAG_L3_CONT
            } else {
                0
            };
        for addr in (start..end).step_by(PAGESIZE) {
            table0.map_to(addr, addr, flag, &mut allocator)?;
        }

        // DATA and BSS.
        let start = get_data_start();
        let end = get_stack_memory();
        let flag = kernel_page_flag_rw()
            | if (end - start) / PAGESIZE as u64 > 1 {
                FLAG_L3_CONT
            } else {
                0
            };
        for addr in (start..end).step_by(PAGESIZE) {
            table0.map_to(addr, addr, flag, &mut allocator)?;
        }

        // Stack memory.
        let flag = kernel_page_flag_rw() | FLAG_L3_CONT;
        let mut addr = get_stack_memory();
        for _ in 0..self.num_cpus {
            let end = addr + STACK_SIZE as u64;
            addr += PAGESIZE as u64; // canary

            for phy_addr in (addr..end).step_by(PAGESIZE) {
                table0.map_to(phy_addr, phy_addr, flag, &mut allocator)?;
            }

            addr = end;
        }

        // Device memory.
        let flag = device_page_flag();
        for range in self.device_ranges.iter() {
            if let Some(range) = range {
                let flag = if range.end - range.start > PAGESIZE {
                    flag | FLAG_L3_CONT
                } else {
                    flag
                };
                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator)?;
                }
            }
        }

        // Read-only memory.
        let flag = kernel_page_flag_ro();
        for range in self.ro_ranges.iter() {
            if let Some(range) = range {
                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator)?;
                }
            }
        }

        // Heap memory without L3 cache.
        // This region will be used to manipulate page tables.
        let flag = kernel_page_flag_rw_no_cache() | FLAG_L3_CONT;
        for heap in self.heap {
            if let Some(range) = heap {
                let flag = if range.end - range.start > PAGESIZE {
                    flag | FLAG_L3_CONT
                } else {
                    flag
                };

                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator)?;
                }
            }
        }

        // Heap memory with L3 cache.
        let mut addr = HEAP_START;
        let flag = kernel_page_flag_rw();
        while let Some(frame) = allocator.allocate_frame() {
            if table0
                .map_to(addr as u64, frame, flag, &mut allocator)
                .is_none()
            {
                break;
            }

            addr += PAGESIZE;
        }

        let heap_size = (addr - HEAP_START) as usize;

        self.table0 = Some(table0);
        self.heap_size = Some(heap_size);

        Some(())
    }

    /// Return the length of heap memory.
    pub unsafe fn init(&mut self) -> Result<(), &'static str> {
        // check for 4KiB granule and at least 36 bits physical address bus
        let mmfr = id_aa64mmfr0_el1::get();
        let b = mmfr & 0xF;
        if b < 1
        /* 36 bits */
        {
            return Err(err_msg!("36-bit address space is not supported."));
        }

        if mmfr & (0xF << 28) != 0
        /* 4KiB */
        {
            return Err(err_msg!("4KiB granule not support."));
        }

        self.init_memory_map()
            .ok_or(err_msg!("failed init_memory_map()"))?; // Initialize TTBR0.

        Ok(())
    }

    pub unsafe fn print(&self) {
        unsafe_puts("num_cpu = 0x");
        unsafe_print_hex_u32(self.num_cpus as u32);
        unsafe_puts("\n");

        unsafe fn print_range(range: &Option<MemoryRange>) {
            if let Some(r) = range {
                unsafe_puts("    0x");
                unsafe_print_hex_u64(r.start as u64);
                unsafe_puts(" - 0x");
                unsafe_print_hex_u64(r.end as u64);
                unsafe_puts("\n");
            }
        }

        unsafe_puts("Device Memory:\n");
        for range in self.device_ranges.iter() {
            print_range(&range);
        }

        unsafe_puts("Heap Memory:\n");
        for range in self.heap.iter() {
            print_range(range);
        }

        unsafe_puts("Read-only Memory:\n");
        for range in self.ro_ranges.iter() {
            print_range(range);
        }

        let start = get_kernel_start() as usize;
        let end = get_stack_memory() as usize;

        unsafe_puts("Kernel:\n");
        unsafe_puts("    0x");
        unsafe_print_hex_u64(start as u64);
        unsafe_puts(" - 0x");
        unsafe_print_hex_u64(end as u64);
        unsafe_puts("\n");

        let start = end;
        let end = start + STACK_SIZE * self.num_cpus;

        unsafe_puts("Stack Memory:\n");
        unsafe_puts("    0x");
        unsafe_print_hex_u64(start as u64);
        unsafe_puts(" - 0x");
        unsafe_print_hex_u64(end as u64);
        unsafe_puts("\n");
    }
}

fn get_mair() -> u64 {
    0xFF         | // AttrIdx=0: normal, IWBWA, OWBWA, NTR
    (0x04 <<  8) | // AttrIdx=1: device, nGnRE (must be OSH too)
    (0x44 << 16) // AttrIdx=2: non cacheable
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

/// set registers
pub unsafe fn enable(ttbr0: usize) {
    set_ttbr0(ttbr0);
    init_sp_el1();
}

unsafe fn set_ttbr0(ttbr0: usize) {
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

    // finally, toggle some bits in system control register to enable page translation
    dsb_ish();
    isb();

    let sctlr = sctlr_el1::get();
    let sctlr = update_sctlr(sctlr) & !(1 << 4); // clear SA0

    sctlr_el1::set(sctlr);
    dsb_sy();
    isb();
}
