use core::{
    ptr::{addr_of_mut, write_volatile},
    slice,
};

use super::mbox::{Mbox, MboxChannel};
use awkernel_lib::paging::PAGESIZE;
use embedded_graphics_core::{
    prelude::{DrawTarget, OriginDimensions, RgbColor},
    Pixel,
};

const MBOX_REQUEST: u32 = 0;
const MBOX_TAG_LAST: u32 = 0;

static mut FRMAME_BUFFER_INFO: Option<FramebufferInfo> = None;

/// Framebuffer settings
#[derive(Debug)]
pub struct FramebufferInfo {
    width: u32,
    height: u32,
    pitch: u32,
    is_rgb: bool,
    framebuffer: &'static mut [u8],
    framebuffer_size: usize,
}

impl FramebufferInfo {
    fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8) {
        let pos = (y * self.pitch + x * 4) as usize;

        let pixel = if self.is_rgb {
            r as u32 | (g as u32) << 8 | (b as u32) << 16
        } else {
            b as u32 | (g as u32) << 8 | (r as u32) << 16
        };

        let ptr = (&mut (self.framebuffer[pos])) as *mut u8 as *mut u32;
        unsafe { write_volatile(ptr, pixel) };
    }
}

/// Initializes the linear framebuffer
///
/// # Safety
///
/// This function must be called at initialization.
pub unsafe fn lfb_init(width: u32, height: u32) -> Result<(), &'static str> {
    let channel = MboxChannel::new(8);

    let mut mbox = Mbox::<[u32; 35]>([
        35 * 4,
        MBOX_REQUEST,
        //-----------------------------------------
        0x48003, // Set physical width and height
        8,
        8,
        width,  // Width
        height, // Height
        //-----------------------------------------
        0x48004, // Set virtual width and height
        8,
        8,
        width,  // Virtual width
        height, // Virtual height
        //-----------------------------------------
        0x48009, // Set virtual offset
        8,
        8,
        0, // X offset
        0, // Y offset
        //-----------------------------------------
        0x48005, // Set depth
        4,
        4,
        32, // 32 bits per pixel
        //-----------------------------------------
        0x48006, // Set pixel order
        4,
        4,
        1, // 0: BGR, 1: RGB
        //-----------------------------------------
        0x40001, // Get framebuffer
        8,
        8,
        PAGESIZE as u32, // request: align 4096 bytes, responce: frame buffer base address
        0,               // responce: frame buffer size
        //-----------------------------------------
        0x40008, // Get pitch
        4,
        4,
        0, // Pitch
        //-----------------------------------------
        MBOX_TAG_LAST,
    ]);

    if channel.mbox_call(&mut mbox) && mbox.0[20] == 32 && mbox.0[28] != 0 {
        let framebuffer_address = mbox.0[28] & 0x3FFFFFFF; // Convert GPU address to ARM address
        let framebuffer_size = mbox.0[29] as usize; // Get the frame buffer size in bytes
        let width = mbox.0[5]; // Get actual physical width
        let height = mbox.0[6]; // Get actual physical height
        let pitch = mbox.0[33]; // Get number of bytes per row
        let is_rgb = mbox.0[24] == 1; // Get actual color order

        let framebuffer =
            unsafe { slice::from_raw_parts_mut(framebuffer_address as *mut u8, framebuffer_size) };

        unsafe {
            FRMAME_BUFFER_INFO = Some(FramebufferInfo {
                width,
                height,
                pitch,
                is_rgb,
                framebuffer,
                framebuffer_size,
            });
        }

        Ok(())
    } else {
        Err("Unable to initialize the framebuffer.")
    }
}

pub fn get_frame_buffer_region() -> Option<(usize, usize)> {
    unsafe {
        let info = FRMAME_BUFFER_INFO.as_ref()?;
        Some((info.framebuffer.as_ptr() as usize, info.framebuffer_size))
    }
}

/// Returns the width and height of the framebuffer.
pub fn get_frame_buffer_size() -> Option<(u32, u32)> {
    unsafe {
        let info = FRMAME_BUFFER_INFO.as_ref()?;
        Some((info.width, info.height))
    }
}

pub fn get_framebuffer_info() -> &'static mut Option<FramebufferInfo> {
    unsafe { &mut *addr_of_mut!(FRMAME_BUFFER_INFO) }
}

pub enum FramebufferError {}

impl DrawTarget for FramebufferInfo {
    type Color = embedded_graphics_core::pixelcolor::Rgb888;
    type Error = FramebufferError;

    fn draw_iter<I>(&mut self, pixels: I) -> Result<(), Self::Error>
    where
        I: IntoIterator<Item = embedded_graphics_core::Pixel<Self::Color>>,
    {
        for Pixel(coord, color) in pixels {
            self.set_pixel(
                coord.x as u32,
                coord.y as u32,
                color.r(),
                color.g(),
                color.b(),
            );
        }

        Ok(())
    }
}

impl OriginDimensions for FramebufferInfo {
    fn size(&self) -> embedded_graphics_core::prelude::Size {
        embedded_graphics_core::prelude::Size::new(self.width, self.height)
    }
}
