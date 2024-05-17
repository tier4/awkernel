use core::{
    ptr::{null_mut, slice_from_raw_parts_mut},
    slice,
};

use super::mbox::{Mbox, MboxChannel, MBOX_REQUEST, MBOX_TAG_LAST};
use awkernel_lib::{
    console::{unsafe_print_hex_u64, unsafe_puts},
    graphics::{FrameBuffer, FrameBufferError},
    paging::PAGESIZE,
};
use embedded_graphics::{
    geometry::Point,
    mono_font::MonoTextStyle,
    pixelcolor::Rgb888,
    primitives::{Line, Polyline, Primitive, PrimitiveStyle},
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
    sub_buffer: *mut [u8],
    framebuffer_size: usize,
}

impl FramebufferInfo {
    #[inline(always)]
    fn set_pixel(&mut self, position: Point, color: &Rgb888) {
        let pos = position.y as usize * self.pitch as usize + position.x as usize * 4;

        let buffer = unsafe { &mut *self.sub_buffer };

        if self.is_rgb {
            buffer[pos] = color.r();
            buffer[pos + 1] = color.g();
            buffer[pos + 2] = color.b();
            buffer[pos + 3] = 0;
        } else {
            buffer[pos] = color.b();
            buffer[pos + 1] = color.g();
            buffer[pos + 2] = color.r();
            buffer[pos + 3] = 0;
        }
    }

    #[inline(always)]
    fn init_sub_buffer(&mut self) {
        unsafe {
            if (*self.sub_buffer).len() != 0 || self.framebuffer_size == 0 {
                return;
            }
        }

        let mut buf = alloc::vec::Vec::new();
        buf.resize(self.framebuffer_size, 0);
        self.sub_buffer = buf.leak();
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
                sub_buffer: slice_from_raw_parts_mut(null_mut(), 0),
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
            self.set_pixel(coord, &color);
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
        self.frame_buffer.init_sub_buffer();

        let text = Text::with_alignment(text, position, style, alignment);
        text.draw(&mut self.frame_buffer)
    }

    fn set_pixel(&mut self, position: Point, color: &Rgb888) {
        self.frame_buffer.init_sub_buffer();
        self.frame_buffer.set_pixel(position, color);
    }

    fn fill(&mut self, color: &Rgb888) {
        self.frame_buffer.init_sub_buffer();

        for y in 0..self.frame_buffer.height {
            for x in 0..self.frame_buffer.width {
                self.frame_buffer
                    .set_pixel(Point::new(x as i32, y as i32), color);
            }
        }
    }

    fn line(
        &mut self,
        start: Point,
        end: Point,
        color: &Rgb888,
        stroke_width: u32,
    ) -> Result<(), awkernel_lib::graphics::FrameBufferError> {
        self.frame_buffer.init_sub_buffer();

        Line::new(start, end)
            .into_styled(PrimitiveStyle::with_stroke(*color, stroke_width))
            .draw(&mut self.frame_buffer)?;
        Ok(())
    }

    fn circle(
        &mut self,
        top_left: Point,
        diameter: u32,
        color: &Rgb888,
        stroke_width: u32,
        is_filled: bool,
    ) -> Result<(), FrameBufferError> {
        self.frame_buffer.init_sub_buffer();

        let style = if is_filled {
            PrimitiveStyle::with_fill(*color)
        } else {
            PrimitiveStyle::with_stroke(*color, stroke_width)
        };

        let circle =
            embedded_graphics::primitives::Circle::new(top_left, diameter).into_styled(style);
        circle.draw(&mut self.frame_buffer)?;
        Ok(())
    }

    fn rectangle(
        &mut self,
        corner_1: Point,
        corner_2: Point,
        color: &Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError> {
        self.frame_buffer.init_sub_buffer();

        let style = if is_filled {
            PrimitiveStyle::with_fill(*color)
        } else {
            PrimitiveStyle::with_stroke(*color, stroke_width)
        };

        let rectangle = embedded_graphics::primitives::Rectangle::with_corners(corner_1, corner_2)
            .into_styled(style);
        rectangle.draw(&mut self.frame_buffer)?;
        Ok(())
    }

    fn triangle(
        &mut self,
        vertex_1: Point,
        vertex_2: Point,
        vertex_3: Point,
        color: &Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError> {
        self.frame_buffer.init_sub_buffer();

        let style = if is_filled {
            PrimitiveStyle::with_fill(*color)
        } else {
            PrimitiveStyle::with_stroke(*color, stroke_width)
        };

        let triangle = embedded_graphics::primitives::Triangle::new(vertex_1, vertex_2, vertex_3)
            .into_styled(style);
        triangle.draw(&mut self.frame_buffer)?;
        Ok(())
    }

    fn polyline(
        &mut self,
        points: &[embedded_graphics::prelude::Point],
        color: &embedded_graphics::pixelcolor::Rgb888,
        stroke_width: u32,
    ) -> Result<(), FrameBufferError> {
        self.frame_buffer.init_sub_buffer();

        let style = PrimitiveStyle::with_stroke(*color, stroke_width);

        Polyline::new(&points)
            .into_styled(style)
            .draw(&mut self.frame_buffer)?;

        Ok(())
    }

    fn flush(&mut self) {
        self.inner.init_sub_buffer();
        self.frame_buffer
            .framebuffer
            .copy_from_slice(unsafe { &*self.frame_buffer.sub_buffer });
    }
}
