#![no_std]

extern crate alloc;

use core::time::Duration;

use awkernel_lib::graphics::{bounding_box, circle, draw_mono_text, fill, flush};
use embedded_graphics::{
    geometry::Point,
    mono_font::{ascii::FONT_6X10, MonoTextStyle},
    pixelcolor::{Rgb888, RgbColor},
    text::Alignment,
};

const APP_NAME: &str = "test graphics";

pub async fn run() {
    awkernel_async_lib::spawn(
        APP_NAME.into(),
        test_graphics(),
        awkernel_async_lib::scheduler::SchedulerType::PrioritizedFIFO(0),
    )
    .await;
}

async fn test_graphics() {
    // Get the bounding box of the screen.
    let bbox = bounding_box();
    let mut x = 20;
    let mut y = 20;
    let mut x_direction = 5;
    let mut y_direction = 5;
    let radius = 20;

    let text_style = MonoTextStyle::new(&FONT_6X10, Rgb888::WHITE);

    loop {
        // Fill the screen with black
        fill(&Rgb888::BLACK);

        // Draw a red circle
        let _ = circle(
            Point::new(x - radius, y - radius),
            radius as u32 * 2,
            &Rgb888::RED,
            1,
            true,
        );

        // Draw a text
        let _ = draw_mono_text(
            "Hello, Awernel!",
            Point::new(bbox.size.width as i32 / 2, bbox.size.height as i32 - 10),
            text_style,
            Alignment::Center,
        );

        // Refresh the screen
        flush();

        // Update the position
        x += x_direction;
        y += y_direction;

        // Bounce the circle off the edges of the screen
        if x - radius <= 0 || x + radius >= bbox.size.width as i32 {
            x_direction = -x_direction;
        }
        if y - radius <= 0 || y + radius >= bbox.size.height as i32 {
            y_direction = -y_direction;
        }

        // Wait for a while
        awkernel_async_lib::sleep(Duration::from_millis(50)).await;
    }
}
