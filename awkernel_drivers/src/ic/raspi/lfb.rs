use core::slice;

use super::mbox::{Mbox, MboxChannel, MBOX_REQUEST, MBOX_TAG_LAST};
use awkernel_lib::{
    console::{unsafe_print_hex_u64, unsafe_puts},
    graphics::{FrameBuffer, FrameBufferError},
    paging::PAGESIZE,
};
use embedded_graphics::{
    mono_font::MonoTextStyle,
    text::{Alignment, Text},
    Drawable,
};
use embedded_graphics_core::{
    geometry::Dimensions,
    prelude::{DrawTarget, OriginDimensions, RgbColor},
    Pixel,
};

static mut RASPI_FRAME_BUFFER: Option<RaspiFrameBuffer> = None;

/// Framebuffer settings
#[derive(Debug)]
struct FramebufferInfo {
    width: u32,
    height: u32,
    pitch: u32,
    is_rgb: bool,
    framebuffer: &'static mut [u8],
    framebuffer_size: usize,
}

impl FramebufferInfo {
    #[inline(always)]
    fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8) {
        let pos = (y * self.pitch + x * 4) as usize;

        if self.is_rgb {
            self.framebuffer[pos] = r;
            self.framebuffer[pos + 1] = g;
            self.framebuffer[pos + 2] = b;
            self.framebuffer[pos + 3] = 0;
        } else {
            self.framebuffer[pos] = b;
            self.framebuffer[pos + 1] = g;
            self.framebuffer[pos + 2] = r;
            self.framebuffer[pos + 3] = 0;
        }
    }
}

/// Initializes the linear framebuffer
///
/// # Safety
///
/// This function must be called at initialization.
pub unsafe fn lfb_init(width: u32, height: u32) -> Result<(), &'static str> {
    let channel = MboxChannel::new();

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

        unsafe {
            unsafe_puts("Frame buffer: addr = 0x");
            unsafe_print_hex_u64(mbox.0[28] as u64);
            unsafe_puts("\r\n");
        }

        let framebuffer =
            unsafe { slice::from_raw_parts_mut(framebuffer_address as *mut u8, framebuffer_size) };

        let raspi_framebuffer = RaspiFrameBuffer {
            frame_buffer: FramebufferInfo {
                width,
                height,
                pitch,
                is_rgb,
                framebuffer,
                framebuffer_size,
            },
        };

        unsafe {
            RASPI_FRAME_BUFFER = Some(raspi_framebuffer);
            awkernel_lib::graphics::set_frame_buffer(RASPI_FRAME_BUFFER.as_mut().unwrap());
        }

        Ok(())
    } else {
        Err("Unable to initialize the framebuffer.")
    }
}

pub fn get_frame_buffer_region() -> Option<(usize, usize)> {
    unsafe {
        let rfb = RASPI_FRAME_BUFFER.as_ref()?;
        Some((
            rfb.frame_buffer.framebuffer.as_ptr() as usize,
            rfb.frame_buffer.framebuffer_size,
        ))
    }
}

impl DrawTarget for FramebufferInfo {
    type Color = embedded_graphics_core::pixelcolor::Rgb888;
    type Error = FrameBufferError;

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

#[derive(Debug)]
struct RaspiFrameBuffer {
    frame_buffer: FramebufferInfo,
}

impl FrameBuffer for RaspiFrameBuffer {
    fn bounding_box(&self) -> embedded_graphics_core::primitives::Rectangle {
        self.frame_buffer.bounding_box()
    }

    fn draw_mono_text(
        &mut self,
        text: &str,
        position: embedded_graphics_core::prelude::Point,
        style: MonoTextStyle<'static, embedded_graphics_core::pixelcolor::Rgb888>,
        alignment: Alignment,
    ) -> Result<embedded_graphics_core::prelude::Point, awkernel_lib::graphics::FrameBufferError>
    {
        let text = Text::with_alignment(text, position, style, alignment);
        text.draw(&mut self.frame_buffer)
    }

    fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8) {
        self.frame_buffer.set_pixel(x, y, r, g, b);
    }

    fn fill(&mut self, r: u8, g: u8, b: u8) {
        for y in 0..self.frame_buffer.height {
            for x in 0..self.frame_buffer.width {
                self.frame_buffer.set_pixel(x, y, r, g, b);
            }
        }
    }
}
