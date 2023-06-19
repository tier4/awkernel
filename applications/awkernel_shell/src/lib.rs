#![no_std]

#[macro_use]
extern crate alloc;

use alloc::{boxed::Box, vec::Vec};
use awkernel_async_lib::{
    scheduler::SchedulerType,
    sleep,
    task::{self, TaskResult},
};
use awkernel_lib::{console, sync::mutex::MCSNode, IS_STD};
use blisp::embedded;
use core::time::Duration;

pub fn init() {
    let task_id = task::spawn(
        "awkenel_shell".into(),
        console_handler(),
        SchedulerType::RoundRobin,
    );

    if let Some(irq) = awkernel_lib::console::irq_id() {
        if awkernel_lib::interrupt::register_handler(irq, Box::new(move || task::wake(task_id)))
            .is_err()
        {
            log::error!("Failed to initialize the shell.");
        }
    }
}

async fn console_handler() -> TaskResult {
    let exprs = blisp::init(CODE, vec![Box::new(HelpFfi), Box::new(TaskFfi)]).unwrap();
    let blisp_ctx = blisp::typing(exprs).unwrap();

    let mut line = Vec::new();

    console::print("\nWelcome to Autoware Kernel!\n\n");
    console::print("You can use BLisp language as follows.\n");
    console::print("https://ytakano.github.io/blisp/\n\n");
    console::print("> (factorial 20)\n");
    console::print("2432902008176640000\n");
    console::print("> (+ 10 20)\n");
    console::print("30\n");

    console::print("\nEnjoy!\n\n");

    console::print("> ");
    loop {
        if let Some(c) = console::get() {
            if c == 0x08 || c == 0x7F || c == 0x15 {
                // backspace, delete
                if !line.is_empty() {
                    if !IS_STD {
                        console::put(0x08);
                        console::put(b' ');
                        console::put(0x08);
                    }

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
                    if !IS_STD {
                        console::print("\n");
                    }

                    // Evaluate the line.
                    eval(line_u8, &blisp_ctx);

                    console::print("\n> ");
                } else {
                    console::print("Error: Input string is not UTF-8.");
                }

                line.clear();
            } else {
                // normal character

                if !IS_STD {
                    console::put(c); // echo back
                }

                line.push(c);
            }
        }

        sleep(Duration::from_millis(20)).await;
    }
}

fn eval(expr: &str, ctx: &blisp::semantics::Context) {
    match blisp::eval(expr, ctx) {
        Ok(results) => {
            for result in results {
                match result {
                    Ok(msg) => {
                        console::print(&msg);
                    }
                    Err(e) => {
                        console::print(&e);
                        console::print("\n\ntry as follows\n> (help)\n");
                    }
                }
            }
        }
        Err(err) => {
            console::print(&err.msg);
            console::print("\n\ntry as follows\n> (help)\n");
        }
    }
}

const CODE: &str = "(export factorial (n) (Pure (-> (Int) Int))
    (factorial' n 1))

(defun factorial' (n total) (Pure (-> (Int Int) Int))
    (if (<= n 0)
        total
        (factorial' (- n 1) (* n total))))

(export help () (IO (-> () []))
    (help_ffi))

(export task () (IO (-> () []))
    (task_ffi))
";

#[embedded]
fn help_ffi() {
    console::print("Autoware Kernel v202306\n");
    console::print("BLisp grammer: https://ytakano.github.io/blisp/\n\n");

    console::print("BLisp functions:\n");
    console::print(CODE);
}

#[embedded]
fn task_ffi() {
    let msg = format!("Uptime: {}\n", awkernel_async_lib::uptime(),);
    console::print(&msg);

    print_tasks();

    console::print("\n");

    let msg = format!(
        "Total preemption: {}\n",
        awkernel_async_lib::task::get_num_preemption(),
    );
    console::print(&msg);
}

fn print_tasks() {
    let tasks = task::get_tasks();

    console::print("Tasks:\n");

    let msg = format!(
        "{:>5} {:<10} {:<8} {:>14} {:>14} name\n",
        "ID", "State", "In Queue", "#Preemption", "Last Executed"
    );
    console::print(&msg);

    for t in tasks {
        let mut node = MCSNode::new();
        let info = t.info.lock(&mut node);

        let state = format!("{:?}", info.get_state());

        let msg = format!(
            "{:>5} {:<10} {:<8} {:>14} {:>14} {}\n",
            t.id,
            state,
            info.in_queue(),
            info.get_num_preemption(),
            info.get_last_executed(),
            t.name,
        );

        console::print(&msg);
    }
}
