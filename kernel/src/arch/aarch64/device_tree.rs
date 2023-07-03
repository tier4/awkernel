use awkernel_lib::{
    device_tree::{device_tree::DeviceTree, error::DeviceTreeError},
    static_alloc,
};
use core::{mem::MaybeUninit, ptr::write_volatile};

const DEVICE_TREE_MEMORY_SIZE: usize = 1024 * 1024 * 4;

static mut MEMORY_POOL: [MaybeUninit<u8>; DEVICE_TREE_MEMORY_SIZE] =
    [MaybeUninit::new(0); DEVICE_TREE_MEMORY_SIZE];
static mut LOCAL_TLSF: Option<static_alloc::TLSF> = None;
static mut LOCAL_ALLOCATOR: Option<static_alloc::StaticAlloc> = None;

pub fn from_bytes<'a>(
    bytes: &'a [u8],
) -> Result<DeviceTree<'a, static_alloc::StaticAlloc<'static>>, DeviceTreeError> {
    let allocator = unsafe { get_allocator() };

    DeviceTree::from_bytes(bytes, allocator.clone())
}

unsafe fn get_allocator() -> &'static mut static_alloc::StaticAlloc<'static> {
    if let Some(allocator) = &mut LOCAL_ALLOCATOR {
        return allocator;
    }

    let tlsf = static_alloc::TLSF::new(&mut MEMORY_POOL);

    write_volatile(&mut LOCAL_TLSF, Some(tlsf));

    let ref_tlsf = LOCAL_TLSF.as_mut().unwrap();

    let allocator = static_alloc::StaticAlloc::new(ref_tlsf);

    write_volatile(&mut LOCAL_ALLOCATOR, Some(allocator));

    LOCAL_ALLOCATOR.as_mut().unwrap()
}
