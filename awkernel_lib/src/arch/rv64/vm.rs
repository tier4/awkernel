use super::address::{PhysPageNum, VirtPageNum};
use super::frame_allocator::{frame_alloc, FrameTracker};
use super::page_table::{Flags as PTEFlags, PageTable, PageTableEntry};
use crate::addr::{virt_addr::VirtAddr, Addr};
use crate::{console::unsafe_puts, paging::PAGESIZE};
use alloc::vec::Vec;
use core::arch::asm;
use core::sync::atomic::{AtomicUsize, Ordering};

extern "C" {
    fn stext();
    fn etext();
    fn srodata();
    fn erodata();
    fn sdata();
    fn edata();
    fn sbss_with_stack();
    fn ebss();
    fn ekernel();
}

pub struct MemorySet {
    page_table: PageTable,
    areas: Vec<MapArea>,
}

pub struct MapArea {
    vpn_range: VPNRange,
    data_frames: Vec<FrameTracker>,
    map_type: MapType,
    map_perm: MapPermission,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum MapType {
    Identical,
    Framed,
}

bitflags::bitflags! {
    pub struct MapPermission: u8 {
        const R = 1 << 1;
        const W = 1 << 2;
        const X = 1 << 3;
        const U = 1 << 4;
    }
}

#[derive(Debug, Clone, Copy)]
pub struct VPNRange {
    pub start: VirtPageNum,
    pub end: VirtPageNum,
}

impl VPNRange {
    pub fn new(start: VirtPageNum, end: VirtPageNum) -> Self {
        Self { start, end }
    }
}

impl IntoIterator for VPNRange {
    type Item = VirtPageNum;
    type IntoIter = VPNRangeIterator;

    fn into_iter(self) -> Self::IntoIter {
        VPNRangeIterator {
            current: self.start,
            end: self.end,
        }
    }
}

pub struct VPNRangeIterator {
    current: VirtPageNum,
    end: VirtPageNum,
}

impl Iterator for VPNRangeIterator {
    type Item = VirtPageNum;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current < self.end {
            let vpn = self.current;
            self.current.0 += 1;
            Some(vpn)
        } else {
            None
        }
    }
}

impl MapArea {
    pub fn new(
        start_va: VirtAddr,
        end_va: VirtAddr,
        map_type: MapType,
        map_perm: MapPermission,
    ) -> Self {
        let start_vpn = start_va.floor();
        let end_vpn = end_va.ceil();
        Self {
            vpn_range: VPNRange::new(start_vpn, end_vpn),
            data_frames: Vec::new(),
            map_type,
            map_perm,
        }
    }

    pub fn map_one(&mut self, page_table: &mut PageTable, vpn: VirtPageNum) {
        let ppn: PhysPageNum;
        match self.map_type {
            MapType::Identical => {
                ppn = PhysPageNum(vpn.0);
            }
            MapType::Framed => {
                let frame = frame_alloc().unwrap();
                ppn = frame.ppn;
                self.data_frames.push(frame);
            }
        }
        let pte_flags = PTEFlags::from_bits(self.map_perm.bits()).unwrap();
        page_table.map(vpn, ppn, pte_flags | PTEFlags::V);
    }

    #[allow(dead_code)]
    pub fn unmap_one(&mut self, page_table: &mut PageTable, vpn: VirtPageNum) {
        if self.map_type == MapType::Framed {
            // Find and remove the frame
            let ppn = page_table.translate(vpn).unwrap().ppn();
            self.data_frames.retain(|frame| frame.ppn != ppn);
        }
        page_table.unmap(vpn);
    }

    pub fn map(&mut self, page_table: &mut PageTable) {
        for vpn in self.vpn_range {
            self.map_one(page_table, vpn);
        }
    }

    #[allow(dead_code)]
    pub fn unmap(&mut self, page_table: &mut PageTable) {
        for vpn in self.vpn_range {
            self.unmap_one(page_table, vpn);
        }
    }
}

impl MemorySet {
    pub fn new_bare() -> Self {
        Self {
            page_table: PageTable::new(),
            areas: Vec::new(),
        }
    }

    #[allow(dead_code)]
    pub fn get_heap_size(&self) -> Option<usize> {
        // Return heap size if calculated during init_kernel_heap
        let size = HEAP_SIZE.load(core::sync::atomic::Ordering::Relaxed);
        if size == 0 {
            None
        } else {
            Some(size)
        }
    }

    #[allow(dead_code)]
    pub fn token(&self) -> usize {
        self.page_table.token()
    }

    fn push(&mut self, mut map_area: MapArea, data: Option<&[u8]>) {
        map_area.map(&mut self.page_table);
        if let Some(data) = data {
            map_area.copy_data(&mut self.page_table, data);
        }
        self.areas.push(map_area);
    }

    #[allow(dead_code)]
    pub fn insert_framed_area(
        &mut self,
        start_va: VirtAddr,
        end_va: VirtAddr,
        permission: MapPermission,
    ) {
        self.push(
            MapArea::new(start_va, end_va, MapType::Framed, permission),
            None,
        );
    }

    #[allow(dead_code)]
    pub fn remove_area_with_start_vpn(&mut self, start_vpn: VirtPageNum) {
        if let Some((idx, area)) = self
            .areas
            .iter_mut()
            .enumerate()
            .find(|(_, area)| area.vpn_range.start == start_vpn)
        {
            area.unmap(&mut self.page_table);
            self.areas.remove(idx);
        }
    }

    pub fn new_kernel() -> Self {
        let mut memory_set = Self::new_bare();

        // Detect actual memory end dynamically
        let memory_end = super::get_memory_end();

        // Map kernel sections
        unsafe {
            unsafe_puts("Mapping kernel text section...\r\n");
        }
        memory_set.push(
            MapArea::new(
                VirtAddr::from_usize(stext as usize),
                VirtAddr::from_usize(etext as usize),
                MapType::Identical,
                MapPermission::R | MapPermission::X,
            ),
            None,
        );

        unsafe {
            unsafe_puts("Mapping kernel rodata section...\r\n");
        }
        memory_set.push(
            MapArea::new(
                VirtAddr::from_usize(srodata as usize),
                VirtAddr::from_usize(erodata as usize),
                MapType::Identical,
                MapPermission::R,
            ),
            None,
        );

        unsafe {
            unsafe_puts("Mapping kernel data section...\r\n");
        }
        memory_set.push(
            MapArea::new(
                VirtAddr::from_usize(sdata as usize),
                VirtAddr::from_usize(edata as usize),
                MapType::Identical,
                MapPermission::R | MapPermission::W,
            ),
            None,
        );

        unsafe {
            unsafe_puts("Mapping kernel bss section...\r\n");
        }
        memory_set.push(
            MapArea::new(
                VirtAddr::from_usize(sbss_with_stack as usize),
                VirtAddr::from_usize(ebss as usize),
                MapType::Identical,
                MapPermission::R | MapPermission::W,
            ),
            None,
        );

        unsafe {
            unsafe_puts("Mapping physical memory...\r\n");
            unsafe_puts("  from ekernel: 0x");
            crate::console::unsafe_print_hex_u64(ekernel as usize as u64);
            unsafe_puts("\r\n  to MEMORY_END: 0x");
            crate::console::unsafe_print_hex_u64(memory_end as usize as u64);
            unsafe_puts(" (dynamic)\r\n");
        }
        // Map physical memory range for kernel use
        // This creates an identity mapping for available RAM
        memory_set.push(
            MapArea::new(
                VirtAddr::from_usize(ekernel as usize),
                VirtAddr::from_usize(memory_end as usize),
                MapType::Identical,
                MapPermission::R | MapPermission::W,
            ),
            None,
        );

        memory_set
    }

    pub fn activate(&self) {
        let satp = self.page_table.token();
        unsafe {
            asm!("csrw satp, {}", in(reg) satp);
            asm!("sfence.vma");
        }
    }
    #[allow(dead_code)]
    pub fn translate(&mut self, vpn: VirtPageNum) -> Option<PageTableEntry> {
        self.page_table.translate(vpn)
    }
}

impl MapArea {
    pub fn copy_data(&mut self, page_table: &mut PageTable, data: &[u8]) {
        assert_eq!(self.map_type, MapType::Framed);
        let mut start: usize = 0;
        let mut current_vpn = self.vpn_range.start;
        let len = data.len();
        loop {
            let src = &data[start..len.min(start + PAGESIZE)];
            let dst = &mut page_table
                .translate(current_vpn)
                .unwrap()
                .ppn()
                .get_bytes_array()[..src.len()];
            dst.copy_from_slice(src);
            start += PAGESIZE;
            if start >= len {
                break;
            }
            current_vpn.0 += 1;
        }
    }
}

// Static kernel memory set and heap size tracking
use crate::sync::mcs::MCSNode;
use crate::sync::mutex::Mutex;

pub static KERNEL_SPACE: Mutex<Option<MemorySet>> = Mutex::new(None);
static HEAP_SIZE: AtomicUsize = AtomicUsize::new(0);

pub fn init_kernel_space() {
    let mut node = MCSNode::new();
    let mut kernel_space = KERNEL_SPACE.lock(&mut node);
    let mut memory_set = MemorySet::new_kernel();

    // Calculate dynamic heap size after kernel mapping
    let heap_size = calculate_dynamic_heap_size(&mut memory_set);
    HEAP_SIZE.store(heap_size, Ordering::Relaxed);

    *kernel_space = Some(memory_set);
}

fn calculate_dynamic_heap_size(_memory_set: &mut MemorySet) -> usize {
    extern "C" {
        fn ekernel();
    }
    use crate::addr::{phy_addr::PhyAddr, Addr};

    // Get dynamically detected memory end
    let memory_end_addr = super::get_memory_end();

    // Calculate available memory after kernel
    let kernel_end = PhyAddr::from_usize(ekernel as usize);
    let memory_end = PhyAddr::from_usize(memory_end_addr as usize);

    // Start heap mapping after kernel, aligned to page boundary
    let heap_start_phy =
        PhyAddr::from_usize((kernel_end.as_usize() + PAGESIZE - 1) & !(PAGESIZE - 1));

    if memory_end <= heap_start_phy {
        unsafe {
            unsafe_puts("Warning: No memory available for heap\r\n");
        }
        return 0;
    }

    // Calculate maximum possible heap size
    let max_heap_size = memory_end.as_usize() - heap_start_phy.as_usize();

    unsafe {
        unsafe_puts("Dynamic heap calculation:\r\n");
        unsafe_puts("  Kernel end: 0x");
        crate::console::unsafe_print_hex_u64(kernel_end.as_usize() as u64);
        unsafe_puts("\r\n  Heap start: 0x");
        crate::console::unsafe_print_hex_u64(heap_start_phy.as_usize() as u64);
        unsafe_puts("\r\n  Memory end: 0x");
        crate::console::unsafe_print_hex_u64(memory_end.as_usize() as u64);
        unsafe_puts("\r\n  Max heap size: 0x");
        crate::console::unsafe_print_hex_u64(max_heap_size as u64);
        unsafe_puts("\r\n");
    }

    max_heap_size
}

pub fn activate_kernel_space() {
    let mut node = MCSNode::new();
    let kernel_space = KERNEL_SPACE.lock(&mut node);
    if let Some(ref kernel_space) = *kernel_space {
        kernel_space.activate();
    }
}
#[allow(dead_code)]
pub fn kernel_token() -> usize {
    let mut node = MCSNode::new();
    let kernel_space = KERNEL_SPACE.lock(&mut node);
    if let Some(ref space) = *kernel_space {
        space.page_table.token()
    } else {
        panic!("Kernel space not initialized")
    }
}

pub fn get_heap_size() -> usize {
    let heap_size = HEAP_SIZE.load(Ordering::Relaxed);
    if heap_size == 0 {
        // Fallback calculation if not initialized yet
        extern "C" {
            fn ekernel();
        }
        use crate::addr::{phy_addr::PhyAddr, Addr};

        let memory_end_addr = super::get_memory_end();

        let kernel_end = PhyAddr::from_usize(ekernel as usize);
        let memory_end = PhyAddr::from_usize(memory_end_addr as usize);

        if memory_end > kernel_end {
            memory_end.as_usize() - kernel_end.as_usize()
        } else {
            0
        }
    } else {
        heap_size
    }
}
