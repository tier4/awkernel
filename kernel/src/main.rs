//! # Autoware Kernel
//!
//! Autoware kernel is a safe and realtime operating system.
//! It can execute async/await applications in kernel space safely.

#![feature(start)]
#![feature(abi_x86_interrupt)]
#![feature(allocator_api)]
#![no_main]
#![cfg_attr(not(feature = "std"), no_std)]

extern crate alloc;

use awkernel_async_lib::{
    scheduler::{wake_task, SchedulerType},
    task,
    task::IS_LOAD_RUNNING,
};
use core::{
    fmt::Debug,
    sync::atomic::{AtomicBool, AtomicU16, Ordering},
};
use embedded_graphics::{
    mono_font::{ascii::FONT_10X20, MonoTextStyle},
    pixelcolor::Rgb888,
};
use kernel_info::KernelInfo;

mod arch;
mod config;
mod kernel_info;

#[cfg(not(feature = "std"))]
mod nostd;

static PRIMARY_READY: AtomicBool = AtomicBool::new(false);
static NUM_READY_WORKER: AtomicU16 = AtomicU16::new(0);

/// `main` function is called from each CPU.
/// `kernel_info.cpu_id` represents the CPU identifier.
/// The primary CPU's identifier is 0.
///
/// `Info` of `KernelInfo<Info>` represents architecture specific information.
fn main<Info: Debug>(kernel_info: KernelInfo<Info>) {
    log::info!("CPU#{} is starting.", kernel_info.cpu_id);
    IS_LOAD_RUNNING[kernel_info.cpu_id].store(true, Ordering::Relaxed);

    unsafe { awkernel_lib::cpu::increment_num_cpu() };

    if kernel_info.cpu_id == 0 {
        // Primary CPU.
        IS_LOAD_RUNNING[0].store(false, Ordering::Relaxed);

        let _ = draw_splash();

        #[cfg(not(feature = "std"))]
        awkernel_lib::interrupt::set_preempt_irq(
            config::PREEMPT_IRQ,
            awkernel_async_lib::task::preemption,
        );

        // Set-up timer interrupt.
        #[cfg(not(feature = "std"))]
        if let Some(irq) = awkernel_lib::timer::irq_id() {
            use alloc::boxed::Box;

            awkernel_lib::interrupt::enable_irq(irq);

            let timer_callback = Box::new(|_irq| {
                awkernel_lib::timer::reset();
            });

            if awkernel_lib::interrupt::register_handler(irq, "local timer".into(), timer_callback)
                .is_ok()
            {
                log::info!("A local timer has been initialized.");
            }
        }

        awkernel_lib::sanity::check();

        // Userland.
        task::spawn(
            "main".into(),
            async move { userland::main().await },
            SchedulerType::FIFO,
        );

        NUM_READY_WORKER.store(awkernel_lib::cpu::num_cpu() as u16 - 1, Ordering::SeqCst);

        PRIMARY_READY.store(true, Ordering::SeqCst);

        while NUM_READY_WORKER.load(Ordering::SeqCst) > 0 {
            awkernel_lib::delay::wait_microsec(10);
        }

        loop {
            awkernel_lib::interrupt::disable();

            wake_task(); // Wake executable tasks periodically.
            awkernel_lib::net::poll(); // Poll network devices.

            awkernel_lib::interrupt::enable();

            #[cfg(feature = "std")]
            awkernel_lib::delay::wait_microsec(50);

            #[cfg(not(feature = "std"))]
            {
                if awkernel_lib::timer::is_timer_enabled() {
                    let _int_guard = awkernel_lib::interrupt::InterruptGuard::new();
                    awkernel_lib::interrupt::enable();
                    awkernel_lib::timer::reset();
                    awkernel_lib::delay::wait_interrupt();
                    awkernel_lib::interrupt::disable();
                } else {
                    awkernel_lib::delay::wait_microsec(10);
                }
            }
        }
    }

    // Non-primary CPUs.
    #[cfg(not(feature = "std"))]
    {
        while !PRIMARY_READY.load(Ordering::SeqCst) {
            awkernel_lib::delay::wait_microsec(10);
        }

        awkernel_lib::interrupt::enable_irq(config::PREEMPT_IRQ);

        if let Some(irq) = awkernel_lib::timer::irq_id() {
            awkernel_lib::interrupt::enable_irq(irq);
        }
    }

    NUM_READY_WORKER.fetch_sub(1, Ordering::SeqCst);

    unsafe { task::run() }; // Execute tasks.
}

fn draw_splash() -> Result<(), awkernel_lib::graphics::FrameBufferError> {
    use awkernel_lib::graphics;

    graphics::fill(&Rgb888::new(0, 0, 0));

    let center = graphics::bounding_box().center();
    let white = Rgb888::new(255, 255, 255);

    let character_style = MonoTextStyle::new(&FONT_10X20, white);
    let text = "Welcome to Autoware Kernel v0.1";

    graphics::draw_mono_text(
        text,
        graphics::bounding_box().center() + embedded_graphics::geometry::Point::new(0, 15),
        character_style,
        embedded_graphics::text::Alignment::Center,
    )?;

    // Draw a circle.
    let mut top_left = center;

    top_left.x -= 50;
    top_left.y += 50;

    graphics::circle(top_left, 20, &white, 4, false)?;

    // Draw a cross.
    let mut start = center;
    let mut end = center;

    start.x -= 25;
    start.y += 50;
    end.x = start.x + 20;
    end.y = start.y + 20;

    graphics::line(start, end, &white, 4)?;

    start.x += 20;
    end.x -= 20;
    graphics::line(start, end, &white, 4)?;

    // Draw a triangle.
    let mut vertex_1 = center;
    let mut vertex_2 = center;
    let mut vertex_3 = center;

    vertex_1.x += 15;
    vertex_1.y += 50;
    vertex_2.x += 25;
    vertex_2.y += 70;
    vertex_3.x += 5;
    vertex_3.y += 70;

    graphics::triangle(vertex_1, vertex_2, vertex_3, &white, 4, false)?;

    // Draw a rectangle.
    let mut corner_1 = center;
    let mut corner_2 = center;

    corner_1.x += 35;
    corner_1.y += 50;

    corner_2.x += 55;
    corner_2.y += 70;

    graphics::rectangle(corner_1, corner_2, &white, 4, false)?;

    graphics::flush();

    Ok(())
}
