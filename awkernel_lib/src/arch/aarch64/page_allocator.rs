use core::alloc::Layout;

use crate::{
    addr::{phy_addr::PhyAddr, virt_addr::VirtAddr},
    paging::{self, Frame, PAGESIZE},
};

const NUM_RANGES: usize = 16;

#[derive(Debug, Clone, Copy)]
pub struct Page {
    frame: PhyAddr,
}

impl Frame for Page {
    fn start_address(&self) -> crate::addr::phy_addr::PhyAddr {
        self.frame
    }

    fn set_address(&mut self, addr: PhyAddr) {
        self.frame = addr;
    }

    fn size(&self) -> usize {
        PAGESIZE
    }
}

impl Page {
    pub fn new(frame: PhyAddr) -> Self {
        Page { frame }
    }
}

pub struct PageAllocator<F: crate::paging::Frame + Copy> {
    range: [Option<(F, F)>; NUM_RANGES],
    idx: usize,
    current: usize,
}

impl crate::paging::FrameAllocator<Page, &'static str> for PageAllocator<Page> {
    fn allocate_frame(&mut self) -> Result<Page, &'static str> {
        let Some(range) = self.range.get_mut(self.current) else {
            return Err("no more page range");
        };

        let page_size = PhyAddr::new(PAGESIZE);

        if let Some(range) = range {
            let result = range.0;

            range.0.set_address(range.0.start_address() + page_size);

            if range.0.start_address() >= range.1.start_address() {
                self.current += 1;
            }

            Ok(result)
        } else {
            Err("no more page")
        }
    }
}

impl<F: crate::paging::Frame + Copy> PageAllocator<F> {
    pub fn new() -> Self {
        PageAllocator {
            range: [None; NUM_RANGES],
            idx: 0,
            current: 0,
        }
    }

    pub fn push(&mut self, start: F, end: F) -> Result<(), &'static str> {
        if start.start_address() >= end.start_address() {
            return Err("start >= end");
        }

        if self.idx >= self.range.len() {
            return Err("too many heap ranges");
        }

        self.range[self.idx] = Some((start, end));
        self.idx += 1;

        Ok(())
    }
}

impl<F: crate::paging::Frame + Copy> Default for PageAllocator<F> {
    fn default() -> Self {
        Self::new()
    }
}

pub struct HeapPageAllocator;

impl crate::paging::FrameAllocator<Page, &'static str> for HeapPageAllocator {
    fn allocate_frame(&mut self) -> Result<Page, &'static str> {
        let layout = Layout::from_size_align(PAGESIZE, PAGESIZE).or(Err("invalid layout"))?;
        let ptr = unsafe { alloc::alloc::alloc(layout) };

        if ptr.is_null() {
            return Err("out of memory");
        }

        let phy_addr = paging::vm_to_phy(VirtAddr::new(ptr as usize))
            .ok_or("failed to translate VM to Phy")?;

        Ok(Page::new(phy_addr))
    }
}
