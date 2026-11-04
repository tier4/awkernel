use core::{
    ptr::{slice_from_raw_parts_mut, NonNull},
    slice,
};

use super::mbox::{
    msg::{Buffer as MboxBuffer, Tag},
    Caching, Error, TagId,
};
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

use alloc::vec;

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
        if position.y < 0
            || position.y >= self.height as i32
            || position.x < 0
            || position.x >= self.width as i32
        {
            return;
        }

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
            if let Some(buf) = self.sub_buffer.as_ref() {
                if !buf.is_empty() || self.framebuffer_size == 0 {
                    return;
                }
            }
        }

        let buf = vec![0; self.framebuffer_size];
        self.sub_buffer = buf.leak();
    }
}

#[repr(C)]
struct InitializeTag {
    phys_display: Tag<(u32, u32), (u32, u32)>,
    virt_display: Tag<(u32, u32), (u32, u32)>,
    virtual_offset: Tag<(u32, u32), (u32, u32)>,
    pixel_depth: Tag<u32, u32>,
    pixel_order: Tag<u32, u32>,
    allocate_buffer: Tag<u32, (u32, u32)>,
    get_pixel_pitch: Tag<(), u32>,
}

impl InitializeTag {
    pub const fn new(width: u32, depth: u32, pixel_depth: u32, rgb: bool, page_size: u32) -> Self {
        Self {
            phys_display: Tag::new(TagId::SetPhysDisplaySize, (width, depth)),
            virt_display: Tag::new(TagId::SetVirtDisplaySize, (width, depth)),
            virtual_offset: Tag::new(TagId::SetVirtualOffset, (0, 0)),
            pixel_depth: Tag::new(TagId::SetFrameBufferDepth, pixel_depth),
            pixel_order: Tag::new(TagId::SetPixelOrder, rgb as u32),
            allocate_buffer: Tag::new(TagId::AllocateBuffer, page_size),
            get_pixel_pitch: Tag::new(TagId::GetPixelPitch, ()),
        }
    }
}

/// Initializes the linear framebuffer
///
/// # Safety
///
/// This function must be called at initialization.
pub unsafe fn lfb_init(width: u32, height: u32) -> Result<(), Error> {
    let mut mbox = MboxBuffer::new(InitializeTag::new(width, height, 32, true, PAGESIZE as u32));
    mbox.call(Caching::Uncached)?;
    let tags = mbox.tags();

    let (buffer_addr, buffer_size) = *tags.allocate_buffer.try_response()?;
    if buffer_addr == 0 || buffer_size == 0 {
        return Err(Error::Unsuccessful);
    }
    let is_rgb = *tags.pixel_order.try_response()? != 0;
    let pitch = *mbox.tags().get_pixel_pitch.try_response()?;

    let buffer_addr = (buffer_addr & 0x3fff_ffff) as usize; // Convert to physical address
    let framebuffer_size = buffer_size as usize;

    unsafe {
        unsafe_puts("Frame buffer: addr = 0x");
        unsafe_print_hex_u64(buffer_addr as u64);
        unsafe_puts("\r\n");
    }

    let framebuffer =
        unsafe { slice::from_raw_parts_mut(buffer_addr as *mut u8, framebuffer_size) };

    let raspi_framebuffer = RaspiFrameBuffer {
        frame_buffer: FramebufferInfo {
            width,
            height,
            pitch,
            is_rgb,
            framebuffer,
            sub_buffer: slice_from_raw_parts_mut(NonNull::dangling().as_ptr(), 0),
            framebuffer_size,
        },
    };

    unsafe {
        RASPI_FRAME_BUFFER = Some(raspi_framebuffer);
        let ptr = &raw mut RASPI_FRAME_BUFFER;
        awkernel_lib::graphics::set_frame_buffer((*ptr).as_mut().unwrap());
    }

    Ok(())
}

pub fn get_frame_buffer_region() -> Option<(usize, usize)> {
    unsafe {
        let ptr = &raw mut RASPI_FRAME_BUFFER;
        let rfb = (*ptr).as_ref()?;
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

        Polyline::new(points)
            .into_styled(style)
            .draw(&mut self.frame_buffer)?;

        Ok(())
    }

    fn flush(&mut self) {
        self.frame_buffer.init_sub_buffer();
        self.frame_buffer
            .framebuffer
            .copy_from_slice(unsafe { &*self.frame_buffer.sub_buffer });
    }
}
