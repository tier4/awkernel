#![no_std]

extern crate alloc;

use alloc::format;
use awkernel_lib::graphics::{self, FrameBufferError};
use core::time::Duration;
use embedded_graphics::{
    mono_font::{
        MonoTextStyle,
        ascii::{FONT_8X13, FONT_10X20},
    },
    pixelcolor::Rgb888,
};

pub async fn run() {
    let mut x = false;
    loop {
        let _ = draw(x);
        awkernel_async_lib::sleep(Duration::from_secs(5)).await;
        x = !x;
    }
}

fn draw(x: bool) -> Result<(), FrameBufferError> {
    graphics::fill(&Rgb888::new(0, 0, 0));

    let mut top_left = graphics::bounding_box().top_left;
    top_left.y += 15;
    top_left.x += 5;

    // Clear screen.
    let white = Rgb888::new(255, 255, 255);

    // Print "Awkernel"
    let character_style = MonoTextStyle::new(&FONT_10X20, white);
    let text = format!("{} Awkernel v0.1", if x { "/(^_^)\\" } else { "\\(^_^)/" });

    graphics::draw_mono_text(
        &text,
        top_left,
        character_style,
        embedded_graphics::text::Alignment::Left,
    )?;

    let step = 13;

    let mut top_left = graphics::bounding_box().top_left;
    top_left.y += 15 + step;
    top_left.x += 5;
    let character_style = MonoTextStyle::new(&FONT_8X13, white);
    let mut n = 0;

    // Print interfaces.
    let ifs = awkernel_lib::net::get_all_interface();
    for netif in ifs.iter() {
        let msg = format!("{netif}");
        for line in msg.lines() {
            let mut pos = top_left;
            pos.y += n * step;

            graphics::draw_mono_text(
                line,
                pos,
                character_style,
                embedded_graphics::text::Alignment::Left,
            )?;

            n += 1;
        }
    }

    graphics::flush();

    Ok(())
}
