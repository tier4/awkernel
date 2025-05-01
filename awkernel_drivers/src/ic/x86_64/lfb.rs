use core::ptr::{slice_from_raw_parts_mut, NonNull};

use awkernel_lib::graphics::{FrameBuffer, FrameBufferError};
use bootloader_api::info::{FrameBufferInfo, PixelFormat};
use embedded_graphics::{
    draw_target::DrawTarget,
    geometry::{Dimensions, OriginDimensions},
    pixelcolor::RgbColor,
    primitives::{Polyline, Primitive, PrimitiveStyle},
    text::Text,
    Drawable, Pixel,
};

use alloc::vec;

static mut X86_FRAME_BUFFER: Option<X86FrameBuffer> = None;

/// # Safety
///
/// This function must be called at initialization.
pub unsafe fn init(info: FrameBufferInfo, buffer: &'static mut [u8]) {
    log::debug!("Frame buffer has been initialized: {info:?}");

    X86_FRAME_BUFFER = Some(X86FrameBuffer {
        inner: X86FrameBufferInner {
            info,
            buffer,
            sub_buffer: slice_from_raw_parts_mut(NonNull::dangling().as_ptr(), 0),
        },
    });

    let ptr = &raw mut X86_FRAME_BUFFER;
    awkernel_lib::graphics::set_frame_buffer((*ptr).as_mut().unwrap());
}

struct X86FrameBufferInner {
    info: FrameBufferInfo,
    buffer: &'static mut [u8],
    sub_buffer: *mut [u8],
}

impl X86FrameBufferInner {
    #[inline(always)]
    fn set_pixel(
        &mut self,
        position: embedded_graphics::geometry::Point,
        color: &embedded_graphics::pixelcolor::Rgb888,
    ) {
        if position.x < 0
            || position.x >= self.info.width as i32
            || position.y < 0
            || position.y >= self.info.height as i32
        {
            return;
        }

        let x = position.x as usize;
        let y = position.y as usize;
        let bytes_per_line = self.info.bytes_per_pixel * self.info.stride;
        let pos = y * bytes_per_line + x * self.info.bytes_per_pixel;

        let buffer = unsafe { &mut *self.sub_buffer };

        match self.info.pixel_format {
            PixelFormat::Rgb => {
                buffer[pos] = color.r();
                buffer[pos + 1] = color.g();
                buffer[pos + 2] = color.b();
            }
            PixelFormat::Bgr => {
                buffer[pos] = color.b();
                buffer[pos + 1] = color.g();
                buffer[pos + 2] = color.r();
            }
            PixelFormat::U8 => {
                let v =
                    0.299 * color.r() as f64 + 0.587 * color.g() as f64 + 0.114 * color.b() as f64;
                buffer[pos] = v as u8;
            }
            PixelFormat::Unknown {
                red_position,
                green_position,
                blue_position,
            } => {
                buffer[pos + red_position as usize] = color.r();
                buffer[pos + green_position as usize] = color.g();
                buffer[pos + blue_position as usize] = color.b();
            }
            _ => {}
        }
    }

    #[inline(always)]
    fn init_sub_buffer(&mut self) {
        unsafe {
            if let Some(buf) = self.sub_buffer.as_ref() {
                if !buf.is_empty() {
                    return;
                }
            }
        }

        let buf = vec![0; self.buffer.len()];
        self.sub_buffer = buf.leak();
    }
}

impl DrawTarget for X86FrameBufferInner {
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

impl OriginDimensions for X86FrameBufferInner {
    fn size(&self) -> embedded_graphics_core::prelude::Size {
        embedded_graphics_core::prelude::Size::new(self.info.width as u32, self.info.height as u32)
    }
}

struct X86FrameBuffer {
    inner: X86FrameBufferInner,
}

impl FrameBuffer for X86FrameBuffer {
    fn draw_mono_text(
        &mut self,
        text: &str,
        position: embedded_graphics::geometry::Point,
        style: embedded_graphics::mono_font::MonoTextStyle<
            'static,
            embedded_graphics::pixelcolor::Rgb888,
        >,
        alignment: embedded_graphics::text::Alignment,
    ) -> Result<embedded_graphics::geometry::Point, FrameBufferError> {
        self.inner.init_sub_buffer();

        let text = Text::with_alignment(text, position, style, alignment);
        text.draw(&mut self.inner)
    }

    fn bounding_box(&self) -> embedded_graphics::primitives::Rectangle {
        self.inner.bounding_box()
    }

    fn set_pixel(
        &mut self,
        position: embedded_graphics::geometry::Point,
        color: &embedded_graphics::pixelcolor::Rgb888,
    ) {
        self.inner.init_sub_buffer();

        self.inner.set_pixel(position, color);
    }

    fn fill(&mut self, color: &embedded_graphics::pixelcolor::Rgb888) {
        self.inner.init_sub_buffer();

        for y in 0..self.inner.info.height {
            for x in 0..self.inner.info.width {
                self.inner.set_pixel(
                    embedded_graphics::geometry::Point::new(x as i32, y as i32),
                    color,
                );
            }
        }
    }

    fn circle(
        &mut self,
        top_left: embedded_graphics::prelude::Point,
        diameter: u32,
        color: &embedded_graphics::pixelcolor::Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError> {
        self.inner.init_sub_buffer();

        let style = if is_filled {
            PrimitiveStyle::with_fill(*color)
        } else {
            PrimitiveStyle::with_stroke(*color, stroke_width)
        };

        let circle =
            embedded_graphics::primitives::Circle::new(top_left, diameter).into_styled(style);
        circle.draw(&mut self.inner)?;
        Ok(())
    }

    fn line(
        &mut self,
        start: embedded_graphics::prelude::Point,
        end: embedded_graphics::prelude::Point,
        color: &embedded_graphics::pixelcolor::Rgb888,
        stroke_width: u32,
    ) -> Result<(), FrameBufferError> {
        self.inner.init_sub_buffer();

        let line = embedded_graphics::primitives::Line::new(start, end)
            .into_styled(PrimitiveStyle::with_stroke(*color, stroke_width));
        line.draw(&mut self.inner)?;

        Ok(())
    }

    fn rectangle(
        &mut self,
        corner_1: embedded_graphics::prelude::Point,
        corner_2: embedded_graphics::prelude::Point,
        color: &embedded_graphics::pixelcolor::Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError> {
        self.inner.init_sub_buffer();

        let style = if is_filled {
            PrimitiveStyle::with_fill(*color)
        } else {
            PrimitiveStyle::with_stroke(*color, stroke_width)
        };

        let rectangle = embedded_graphics::primitives::Rectangle::with_corners(corner_1, corner_2)
            .into_styled(style);
        rectangle.draw(&mut self.inner)?;

        Ok(())
    }

    fn triangle(
        &mut self,
        vertex_1: embedded_graphics::prelude::Point,
        vertex_2: embedded_graphics::prelude::Point,
        vertex_3: embedded_graphics::prelude::Point,
        color: &embedded_graphics::pixelcolor::Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError> {
        self.inner.init_sub_buffer();

        let style = if is_filled {
            PrimitiveStyle::with_fill(*color)
        } else {
            PrimitiveStyle::with_stroke(*color, stroke_width)
        };

        let triangle = embedded_graphics::primitives::Triangle::new(vertex_1, vertex_2, vertex_3)
            .into_styled(style);
        triangle.draw(&mut self.inner)?;

        Ok(())
    }

    fn polyline(
        &mut self,
        points: &[embedded_graphics::prelude::Point],
        color: &embedded_graphics::pixelcolor::Rgb888,
        stroke_width: u32,
    ) -> Result<(), FrameBufferError> {
        self.inner.init_sub_buffer();

        let style = PrimitiveStyle::with_stroke(*color, stroke_width);

        Polyline::new(points)
            .into_styled(style)
            .draw(&mut self.inner)?;

        Ok(())
    }

    fn flush(&mut self) {
        self.inner.init_sub_buffer();
        self.inner
            .buffer
            .copy_from_slice(unsafe { &*self.inner.sub_buffer });
    }
}
