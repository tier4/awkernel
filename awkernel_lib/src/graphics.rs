use embedded_graphics::{
    geometry::{Point, Size},
    mono_font::MonoTextStyle,
    primitives::Rectangle,
    text::Alignment,
};
use embedded_graphics_core::pixelcolor::Rgb888;

pub enum FrameBufferError {
    NoFrameBuffer,
}

static mut FRAME_BUFFER: Option<&'static mut dyn FrameBuffer> = None;

pub trait FrameBuffer {
    fn draw_mono_text(
        &mut self,
        text: &str,
        position: Point,
        style: MonoTextStyle<'static, Rgb888>,
        alignment: Alignment,
    ) -> Result<Point, FrameBufferError>;

    fn bounding_box(&self) -> Rectangle;

    fn set_pixel(&mut self, x: u32, y: u32, r: u8, g: u8, b: u8);

    fn fill(&mut self, r: u8, g: u8, b: u8);
}

/// # Safety
///
/// This function must be called only once at initialization.
pub unsafe fn set_frame_buffer(frame_buffer: &'static mut dyn FrameBuffer) {
    FRAME_BUFFER = Some(frame_buffer);
}

#[inline(always)]
pub fn draw_mono_text(
    text: &str,
    position: Point,
    style: MonoTextStyle<'static, Rgb888>,
    alignment: Alignment,
) -> Result<Point, FrameBufferError> {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.draw_mono_text(text, position, style, alignment)
        } else {
            Err(FrameBufferError::NoFrameBuffer)
        }
    }
}

#[inline(always)]
pub fn bounding_box() -> Rectangle {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_ref() {
            frame_buffer.bounding_box()
        } else {
            Rectangle::new(Point::new(0, 0), Size::new(0, 0))
        }
    }
}

#[inline(always)]
pub fn fill(r: u8, g: u8, b: u8) {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.fill(r, g, b);
        }
    }
}

#[inline(always)]
pub fn set_pixel(x: u32, y: u32, r: u8, g: u8, b: u8) {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.set_pixel(x, y, r, g, b);
        }
    }
}
