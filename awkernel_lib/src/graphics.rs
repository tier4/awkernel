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

    fn set_pixel(&mut self, position: Point, color: &Rgb888);

    fn fill(&mut self, color: &Rgb888);

    fn line(
        &mut self,
        start: Point,
        end: Point,
        color: &Rgb888,
        stroke_width: u32,
    ) -> Result<(), FrameBufferError>;

    fn circle(
        &mut self,
        top_left: Point,
        diameter: u32,
        color: &Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError>;
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
pub fn fill(color: &Rgb888) {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.fill(color);
        }
    }
}

#[inline(always)]
pub fn set_pixel(position: Point, color: &Rgb888) {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.set_pixel(position, color);
        }
    }
}

#[inline(always)]
pub fn line(
    start: Point,
    end: Point,
    color: &Rgb888,
    stroke_width: u32,
) -> Result<(), FrameBufferError> {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.line(start, end, color, stroke_width)?;
        }
    }

    Ok(())
}

#[inline(always)]
pub fn circle(
    top_left: Point,
    diameter: u32,
    color: &Rgb888,
    stroke_width: u32,
    is_filled: bool,
) -> Result<(), FrameBufferError> {
    unsafe {
        if let Some(frame_buffer) = FRAME_BUFFER.as_mut() {
            frame_buffer.circle(top_left, diameter, color, stroke_width, is_filled)?;
        }
    }

    Ok(())
}
