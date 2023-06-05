use crate::{
    scheduler::SchedulerType,
    sleep,
    task::{self, TaskResult},
};
use alloc::{boxed::Box, vec::Vec};
use awkernel_lib::console;
use core::time::Duration;

pub fn init() {
    if let Some(irq) = awkernel_lib::console::irq_id() {
        let task_id = task::spawn(console_handler(), SchedulerType::RoundRobin);

        if awkernel_lib::interrupt::register_handler(irq, Box::new(move || task::wake(task_id)))
            .is_err()
        {
            log::error!("Failed to initialize the shell.");
        }
    }
}

async fn console_handler() -> TaskResult {
    let mut line = Vec::new();

    console::print("\nWelcome to Autoware Kernel!\n\n");
    console::print("You can use BLisp language as follows.\n");
    console::print("> (+ 10 20)\n");
    console::print("30\n");

    console::print("\nEnjoy!\n\n");

    console::print("> ");
    loop {
        if let Some(c) = console::get() {
            if c == 0x08 || c == 0x7F || c == 0x15 {
                // backspace, delete
                if !line.is_empty() {
                    console::put(0x08);
                    console::put(b' ');
                    console::put(0x08);
                    line.pop();
                }
                continue;
            } else if c == b'\r' || c == b'\n' {
                // newline
                if line.is_empty() {
                    console::print("\n> ");
                    continue;
                }

                if let Ok(line_u8) = alloc::str::from_utf8(&line) {
                    console::print("\n");
                    console::print(line_u8);

                    console::print("\r\n> ");
                } else {
                    console::print("Error: Input string is not UTF-8.");
                }

                line.clear();
            } else {
                // normal character
                console::put(c);
                line.push(c);
            }
        }

        sleep(Duration::from_millis(100)).await;
    }
}
