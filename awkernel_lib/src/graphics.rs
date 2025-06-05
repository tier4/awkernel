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

    fn rectangle(
        &mut self,
        corner_1: Point,
        corner_2: Point,
        color: &Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError>;

    fn triangle(
        &mut self,
        vertex_1: Point,
        vertex_2: Point,
        vertex_3: Point,
        color: &Rgb888,
        stroke_width: u32, // if `is_filled` is `true`, this parameter is ignored.
        is_filled: bool,
    ) -> Result<(), FrameBufferError>;

    fn polyline(
        &mut self,
        points: &[Point],
        color: &Rgb888,
        stroke_width: u32,
    ) -> Result<(), FrameBufferError>;

    fn flush(&mut self);
}

/// # Safety
///
/// This function must be called only once at initialization.
pub unsafe fn set_frame_buffer(frame_buffer: &'static mut dyn FrameBuffer) {
    FRAME_BUFFER = Some(frame_buffer);
}

/// Draw a text on the frame buffer.
#[inline(always)]
pub fn draw_mono_text(
    text: &str,
    position: Point,
    style: MonoTextStyle<'static, Rgb888>,
    alignment: Alignment,
) -> Result<Point, FrameBufferError> {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.draw_mono_text(text, position, style, alignment)
        } else {
            Err(FrameBufferError::NoFrameBuffer)
        }
    }
}

/// Get the bounding box of the frame buffer.
#[inline(always)]
pub fn bounding_box() -> Rectangle {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.bounding_box()
        } else {
            Rectangle::new(Point::new(0, 0), Size::new(0, 0))
        }
    }
}

/// Fill the frame buffer with a color.
#[inline(always)]
pub fn fill(color: &Rgb888) {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.fill(color);
        }
    }
}

/// Set a pixel on the frame buffer.
#[inline(always)]
pub fn set_pixel(position: Point, color: &Rgb888) {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.set_pixel(position, color);
        }
    }
}

/// Draw a line on the frame buffer.
#[inline(always)]
pub fn line(
    start: Point,
    end: Point,
    color: &Rgb888,
    stroke_width: u32,
) -> Result<(), FrameBufferError> {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.line(start, end, color, stroke_width)?;
        }
    }

    Ok(())
}

/// Draw a circle on the frame buffer.
///
/// If `is_filled` is `true`, the `stroke_width` parameter is ignored, and
/// the circle is filled with the specified color.
/// Otherwise, the circle is drawn with the specified stroke width.
#[inline(always)]
pub fn circle(
    top_left: Point,
    diameter: u32,
    color: &Rgb888,
    stroke_width: u32,
    is_filled: bool,
) -> Result<(), FrameBufferError> {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.circle(top_left, diameter, color, stroke_width, is_filled)?;
        }
    }

    Ok(())
}

/// Draw a rectangle on the frame buffer.
///
/// If `is_filled` is `true`, the `stroke_width` parameter is ignored, and
/// the rectangle is filled with the specified color.
#[inline(always)]
pub fn rectangle(
    corner_1: Point,
    corner_2: Point,
    color: &Rgb888,
    stroke_width: u32,
    is_filled: bool,
) -> Result<(), FrameBufferError> {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.rectangle(corner_1, corner_2, color, stroke_width, is_filled)?;
        }
    }

    Ok(())
}

/// Draw a triangle on the frame buffer.
///
/// If `is_filled` is `true`, the `stroke_width` parameter is ignored, and
/// the triangle is filled with the specified color.
#[inline(always)]
pub fn triangle(
    vertex_1: Point,
    vertex_2: Point,
    vertex_3: Point,
    color: &Rgb888,
    stroke_width: u32,
    is_filled: bool,
) -> Result<(), FrameBufferError> {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.triangle(vertex_1, vertex_2, vertex_3, color, stroke_width, is_filled)?;
        }
    }

    Ok(())
}

/// Draw a polygonal line on the frame buffer.
#[inline(always)]
pub fn polyline(
    points: &[Point],
    color: &Rgb888,
    stroke_width: u32,
) -> Result<(), FrameBufferError> {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.polyline(points, color, stroke_width)?;
        }
    }

    Ok(())
}

/// Flush the frame buffer.
/// This function must be called after drawing operations to refresh the screen.
#[inline(always)]
pub fn flush() {
    unsafe {
        let ptr = &raw mut FRAME_BUFFER;
        if let Some(frame_buffer) = &mut *ptr {
            frame_buffer.flush();
        }
    }
}
