use awkernel_lib::graphics::{FrameBuffer, FrameBufferError};
use bootloader_api::info::{FrameBufferInfo, PixelFormat};
use embedded_graphics::{
    draw_target::DrawTarget,
    geometry::{Dimensions, OriginDimensions},
    pixelcolor::RgbColor,
    text::Text,
    Drawable, Pixel,
};

static mut X86_FRAME_BUFFER: Option<X86FrameBuffer> = None;

/// # Safety
///
/// This function must be called at initialization.
pub unsafe fn init(info: FrameBufferInfo, buffer: &'static mut [u8]) {
    log::debug!("Framebuffer initialized: {:?}", info);

    X86_FRAME_BUFFER = Some(X86FrameBuffer {
        inner: X86FrameBufferInner { info, buffer },
    });

    awkernel_lib::graphics::set_frame_buffer(X86_FRAME_BUFFER.as_mut().unwrap());
}

struct X86FrameBufferInner {
    info: FrameBufferInfo,
    buffer: &'static mut [u8],
}

impl X86FrameBufferInner {
    #[inline(always)]
    fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8) {
        let bytes_per_line = self.info.bytes_per_pixel * self.info.stride;

        match self.info.pixel_format {
            PixelFormat::Rgb => {
                let x = x as usize;
                let y = y as usize;
                let pos = y * bytes_per_line + x * self.info.bytes_per_pixel;
                self.buffer[pos] = r;
                self.buffer[pos + 1] = g;
                self.buffer[pos + 2] = b;
            }
            PixelFormat::Bgr => {
                let x = x as usize;
                let y = y as usize;
                let pos = y * bytes_per_line + x * self.info.bytes_per_pixel;
                self.buffer[pos] = b;
                self.buffer[pos + 1] = g;
                self.buffer[pos + 2] = r;
            }
            PixelFormat::U8 => {
                let x = x as usize;
                let y = y as usize;
                let pos = y * bytes_per_line + x * self.info.bytes_per_pixel;
                self.buffer[pos] = 0xff;
            }
            PixelFormat::Unknown {
                red_position,
                green_position,
                blue_position,
            } => {
                let x = x as usize;
                let y = y as usize;
                let pos = y * bytes_per_line + x * self.info.bytes_per_pixel;
                self.buffer[pos + red_position as usize] = r;
                self.buffer[pos + green_position as usize] = g;
                self.buffer[pos + blue_position as usize] = b;
            }
            _ => {}
        }
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
        let text = Text::with_alignment(text, position, style, alignment);
        text.draw(&mut self.inner)
    }

    fn bounding_box(&self) -> embedded_graphics::primitives::Rectangle {
        self.inner.bounding_box()
    }

    fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8) {
        self.inner.set_pixel(x, y, r, g, b);
    }

    fn fill(&mut self, r: u8, g: u8, b: u8) {
        for y in 0..self.inner.info.height {
            for x in 0..self.inner.info.width {
                self.inner.set_pixel(x as u32, y as u32, r, g, b);
            }
        }
    }
}
