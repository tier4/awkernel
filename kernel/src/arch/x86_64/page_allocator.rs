use x86_64::structures::paging::{FrameAllocator, PhysFrame, Size4KiB};

pub struct PageAllocator<'a> {
    frames: &'a mut dyn Iterator<Item = PhysFrame>,
}

impl<'a> PageAllocator<'a> {
    pub fn new(frames: &'a mut dyn Iterator<Item = PhysFrame>) -> Self {
        PageAllocator { frames }
    }
}

unsafe impl<'a> FrameAllocator<Size4KiB> for PageAllocator<'a> {
    fn allocate_frame(&mut self) -> Option<PhysFrame<Size4KiB>> {
        self.frames.next()
    }
}
