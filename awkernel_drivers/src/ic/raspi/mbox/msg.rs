use super::{Caching, Error, Mbox, MboxChannel, TagId, MBOX_REQUEST, MBOX_TAG_LAST};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};

const TAG_RESPONSE_BIT: u32 = 0x8000_0000;
const TAG_LENGTH_MASK: u32 = 0x7fff_ffff;
const SCRATCH_BYTES: usize = 64;

/// Shared scratch buffer for every [`call`]. A single static is required because the mailbox
/// can only address the low 1 GiB of RAM; an arbitrary task's stack is not guaranteed to live
/// there on a multi-gigabyte system, but a `static` in the kernel image's own .bss reliably does.
static mut SCRATCH: Mbox<[u8; SCRATCH_BYTES]> = Mbox([0; SCRATCH_BYTES]);

/// Serializes access to [`SCRATCH`], the single shared mailbox message buffer.
static SCRATCH_LOCK: Mutex<()> = Mutex::new(());

/// A full mailbox request/response buffer.
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct Buffer<T> {
    buffer_size: u32,
    req_resp_code: u32,
    tags: T,
    end_tag: u32,
}

impl<T> Buffer<T> {
    pub const fn new(tags: T) -> Self {
        Self {
            buffer_size: core::mem::size_of::<Self>() as u32,
            req_resp_code: MBOX_REQUEST,
            tags,
            end_tag: MBOX_TAG_LAST,
        }
    }

    pub const fn tags(&self) -> &T {
        &self.tags
    }

    #[inline]
    pub fn call(&mut self, caching: Caching) -> Result<(), Error> {
        let channel = MboxChannel::new();
        channel.mbox_call_buffer(self, caching)
    }
}

/// Mailbox message tag. Represents a single tag in a mailbox message.
#[repr(C)]
#[derive(Clone, Copy)]
pub(crate) struct Tag<Req: Copy, Res: Copy> {
    tag_id: TagId,
    value_buffer_size: u32,
    req_resp_code: u32,
    payload: TagPayload<Req, Res>,
}

impl<Req: Copy, Res: Copy> Tag<Req, Res> {
    /// Creates new tag with the given ID and request value.
    pub const fn new(tag_id: TagId, req: Req) -> Self {
        let req_len = TagPayload::<Req, Res>::req_size();
        let max_len = TagPayload::<Req, Res>::size();

        Self {
            tag_id,
            value_buffer_size: max_len,
            req_resp_code: req_len,
            payload: TagPayload { req },
        }
    }

    /// Tries to parse payload as a response and, if successful, returns a reference.
    pub const fn try_response(&self) -> Result<&Res, Error> {
        let resp_len = self.req_resp_code;
        if resp_len & TAG_RESPONSE_BIT == 0 {
            return Err(Error::Rejected);
        }
        if (resp_len & TAG_LENGTH_MASK) < core::mem::size_of::<Res>() as u32 {
            return Err(Error::MalformedResponse);
        }
        // SAFETY: the response bit and length were just checked above
        Ok(unsafe { &self.payload.res })
    }
}

/// Union of request and response payloads for a single mailbox tag.
#[repr(C)]
#[derive(Clone, Copy)]
union TagPayload<Req: Copy, Res: Copy> {
    req: Req,
    res: Res,
}

impl<Req: Copy, Res: Copy> TagPayload<Req, Res> {
    const fn req_size() -> u32 {
        core::mem::size_of::<Req>() as u32
    }

    const fn size() -> u32 {
        core::mem::size_of::<Self>() as u32
    }
}

/// Sends a single-tag mailbox request under and returns the typed response.
///
/// # Notes
///
/// Serializes concurrent callers itself (guarding exclusive access to [`SCRATCH`]).
/// Callers do not need their own lock around this call.
pub(crate) fn call<Req: Copy, Res: Copy>(tag_id: TagId, req: Req) -> Result<Res, Error> {
    // TODO is there a way to make sure a stack-allocated buffer is in the low 1 GiB of RAM?
    let body_size = core::mem::size_of::<Buffer<Tag<Req, Res>>>();
    if body_size > SCRATCH_BYTES {
        return Err(Error::BufferTooLarge);
    }

    // Lock the scratch buffer for the duration of this call
    let mut node = MCSNode::new();
    let _guard = SCRATCH_LOCK.lock(&mut node);

    let body_addr = core::ptr::addr_of_mut!(SCRATCH).cast::<Buffer<Tag<Req, Res>>>();
    // SAFETY: `body_ptr` is valid and we have exclusive access to it via the lock above.
    unsafe { body_addr.write_volatile(Buffer::new(Tag::new(tag_id, req))) };
    // SAFETY: `body_ptr` is valid and we have exclusive access to it via the lock above.
    unsafe { &mut *body_addr }.call(Caching::Uncached)?;

    // SAFETY: the firmware has overwritten `scratch` in place with a `Body<Req, Res>`-shaped response.
    let body = unsafe { body_addr.read_volatile() };
    body.tags().try_response().cloned()
}

/// Utility function to send a single-tag GET request via the mailbox using a tag ID.
///
/// `T` is the type of the values sent to the firmware for this tag.
#[inline]
pub(crate) fn get_by_id<T: Copy>(tag: TagId, id: u32) -> Result<T, Error> {
    let (ret_id, val): (u32, T) = call(tag, id)?;
    match ret_id == id {
        true => Ok(val),
        false => Err(Error::ValueMismatch),
    }
}

/// Utility function to send a single-tag SET request via the mailbox using a tag ID.
///
/// `T` is the type of the values sent to the firmware for this tag.
/// `R` is the type of the value returned by the firmware for this tag.
#[inline]
pub(crate) fn set_by_id<T: Copy, R: Copy>(tag: TagId, id: u32, val: T) -> Result<R, Error> {
    let (ret_id, ret_val): (u32, R) = call(tag, (id, val))?;
    match ret_id == id {
        true => Ok(ret_val),
        false => Err(Error::ValueMismatch),
    }
}
