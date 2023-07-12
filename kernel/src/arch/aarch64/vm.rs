use awkernel_lib::{
    arch::aarch64::{
        page_allocator::PageAllocator,
        page_table::{
            flags::{self, FLAG_L3_CONT},
            FrameAllocator, PageTable,
        },
    },
    memory::PAGESIZE,
};

use crate::arch::config::HEAP_START;

pub const STACK_SIZE: u64 = 2 * 1024 * 1024; // 2MiB

extern "C" {
    static __kernel_start: u64;
    static __ro_data_start: u64;
    static __data_start: u64;
    static __stack_memory: u64;
}

pub fn get_kernel_start() -> u64 {
    unsafe { &__kernel_start as *const u64 as u64 }
}

pub fn get_ro_data_start() -> u64 {
    unsafe { &__ro_data_start as *const u64 as u64 }
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
        } else if range.end <= self.start || self.end <= self.start {
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

    ro_ranges: [Option<MemoryRange>; NUM_RANGES],
    rw_ranges: [Option<MemoryRange>; NUM_RANGES],
    exec_ranges: [Option<MemoryRange>; NUM_RANGES],
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
            ro_ranges: [None; NUM_RANGES],
            rw_ranges: [None; NUM_RANGES],
            exec_ranges: [None; NUM_RANGES],
        }
    }

    pub fn set_num_cpus(&mut self, num_cpus: usize) {
        self.num_cpus = num_cpus;
    }

    pub fn push_device_range(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if self.idx_dev >= self.device_ranges.len() {
            return Err("too many device range");
        }

        self.device_ranges[self.idx_dev] = Some(MemoryRange { start, end });
        self.idx_dev += 1;

        Ok(())
    }

    pub fn push_heap(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if start >= end {
            return Err("start >= end");
        }

        if self.idx_heap >= self.heap.len() {
            return Err("too many device range");
        }

        self.heap[self.idx_dev] = Some(MemoryRange { start, end });
        self.idx_heap += 1;

        Ok(())
    }

    /// If
    /// - heap:   `***---------***`
    /// - remove: `*****---*******`
    /// then the heap will be `***--***----***`.
    pub fn remove_heap(&mut self, start: usize, end: usize) -> Result<(), &'static str> {
        if start >= end {
            return Err("start >= end");
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
                    ContainResult::Overlap => return Err("overlap"),
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

    /// Return the length of heap memory.
    pub unsafe fn init(&self) -> usize {
        let mut allocator = PageAllocator::new();
        let mut table0 = PageTable::new(&mut allocator);

        for mem in self.heap.iter() {
            if let Some(m) = mem {
                let _ = allocator.push(m.start as u64, m.end as u64);
            }
        }

        // TEXT.
        let flag = kernel_page_flag_r_exec()
            | if (get_kernel_start() - get_ro_data_start()) / PAGESIZE as u64 > 1 {
                FLAG_L3_CONT
            } else {
                0
            };
        for addr in (get_kernel_start()..get_ro_data_start()).step_by(PAGESIZE) {
            table0.map_to(addr, addr, flag, &mut allocator);
        }

        // Read-only data.
        let flag = kernel_page_flag_ro()
            | if (get_ro_data_start() - get_data_start()) / PAGESIZE as u64 > 1 {
                FLAG_L3_CONT
            } else {
                0
            };
        for addr in (get_ro_data_start()..get_data_start()).step_by(PAGESIZE) {
            table0.map_to(addr, addr, flag, &mut allocator);
        }

        // DATA and BSS.
        let flag = kernel_page_flag_rw()
            | if (get_data_start() - get_stack_memory()) / PAGESIZE as u64 > 1 {
                FLAG_L3_CONT
            } else {
                0
            };
        for addr in (get_ro_data_start()..get_data_start()).step_by(PAGESIZE) {
            table0.map_to(addr, addr, flag, &mut allocator);
        }

        // Stack memory.
        let flag = kernel_page_flag_rw() | FLAG_L3_CONT;
        let mut addr = get_stack_memory();
        for _ in 0..self.num_cpus {
            let end = addr + STACK_SIZE;
            addr += PAGESIZE as u64; // canary

            for phy_addr in (addr..end).step_by(PAGESIZE) {
                table0.map_to(phy_addr, phy_addr, flag, &mut allocator);
            }

            addr = end;
        }

        // Device memory.
        let flag = device_page_flag() | FLAG_L3_CONT;
        for range in self.device_ranges.iter() {
            if let Some(range) = range {
                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator);
                }
            }
        }

        // Read-only memory.
        let flag = kernel_page_flag_ro() | FLAG_L3_CONT;
        for range in self.ro_ranges.iter() {
            if let Some(range) = range {
                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator);
                }
            }
        }

        // Read-write memory.
        let flag = kernel_page_flag_rw() | FLAG_L3_CONT;
        for range in self.rw_ranges.iter() {
            if let Some(range) = range {
                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator);
                }
            }
        }

        // Executable memory.
        let flag = kernel_page_flag_r_exec() | FLAG_L3_CONT;
        for range in self.exec_ranges.iter() {
            if let Some(range) = range {
                for addr in (range.start..range.end).step_by(PAGESIZE) {
                    table0.map_to(addr as u64, addr as u64, flag, &mut allocator);
                }
            }
        }

        // Heap
        let mut addr = HEAP_START;
        let flag = kernel_page_flag_rw();
        while let Some(frame) = allocator.allocate_frame() {
            table0.map_to(addr, frame, flag, &mut allocator);
            addr += PAGESIZE as u64;
        }

        (addr - HEAP_START) as usize
    }
}
