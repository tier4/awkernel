use core::slice;

// Fat pointer representing the packet buffer
// contains a pointer to the real packet data
#[repr(C, packed)]
pub struct MBuf {
    //  pointer to real packet data
    ptr: *mut u8,
    //  data length
    len: usize,
}

unsafe impl Send for MBuf {}

impl MBuf {
    pub fn get_data(&self) {
        let _data = unsafe { slice::from_raw_parts(self.ptr, self.len) };
    }
}
