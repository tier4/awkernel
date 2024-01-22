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
// mod udp;

const SERVICE_NAME: &str = "awkernel shell";

pub fn init() {
    let task_id = task::spawn(SERVICE_NAME.into(), console_handler(), SchedulerType::FIFO);

    if let Some(irq) = awkernel_lib::console::irq_id() {
        if awkernel_lib::interrupt::register_handler(
            irq,
            "serial port (awkernel_shell)",
            Box::new(move |_irq| task::wake(task_id)),
        )
        .is_err()
        {
            log::warn!("Failed to initialize UART's interrupt handler.");
        }
    }
}

async fn console_handler() -> TaskResult {
    log::info!("Start {SERVICE_NAME}.");

    let exprs = blisp::init(
        CODE,
        vec![
            Box::new(HelpFfi),
            Box::new(TaskFfi),
            // Box::new(UdptestFfi),
            Box::new(InterruptFfi),
            Box::new(IfconfigFfi),
        ],
    )
    .unwrap();
    let blisp_ctx = blisp::typing(exprs).unwrap();

    let mut line = Vec::new();

    console::print("\r\nWelcome to Autoware Kernel!\r\n\r\n");
    console::print("You can use BLisp language as follows.\r\n");
    console::print("https://ytakano.github.io/blisp/\r\n\r\n");
    console::print("> (factorial 20)\r\n");
    console::print("2432902008176640000\r\n");
    console::print("> (+ 10 20)\r\n");
    console::print("30\r\n");

    console::print("\r\nEnjoy!\r\n\r\n");

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
                    console::print("\r\n> ");
                    continue;
                }

                if let Ok(line_u8) = alloc::str::from_utf8(&line) {
                    if !IS_STD {
                        console::print("\r\n");
                    }

                    // Evaluate the line.
                    eval(line_u8, &blisp_ctx);

                    console::print("\r\n> ");
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
                        console::print("\r\n\r\ntry as follows\r\n> (help)\r\n");
                    }
                }
            }
        }
        Err(err) => {
            console::print(&err.msg);
            console::print("\r\n\r\ntry as follows\r\n> (help)\r\n");
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

(export interrupt () (IO (-> () []))
    (interrupt_ffi))

(export ifconfig () (IO (-> () []))
    (ifconfig_ffi))

; (export udptest () (IO (-> () []))
;     (udptest_ffi))
";

#[embedded]
fn help_ffi() {
    console::print("Autoware Kernel v202306\r\n");
    console::print("BLisp grammer: https://ytakano.github.io/blisp/\r\n\r\n");

    console::print("BLisp functions:\r\n");
    console::print(CODE);
}

#[embedded]
fn task_ffi() {
    let msg = format!("Uptime: {}\r\n", awkernel_async_lib::uptime(),);
    console::print(&msg);

    print_tasks();

    console::print("\r\n");

    let msg = format!(
        "Total preemption: {}\r\n",
        awkernel_async_lib::task::get_num_preemption(),
    );
    console::print(&msg);

    console::print("Running Tasks:\r\n");
    for task in awkernel_async_lib::task::get_tasks_running().iter() {
        let msg = if task.task_id != 0 {
            format!("  cpu: {:>3}, task: {:>5}\r\n", task.cpu_id, task.task_id)
        } else {
            format!("  cpu: {:>3}, task:\r\n", task.cpu_id)
        };
        console::print(&msg);
    }
}

#[embedded]
fn interrupt_ffi() {
    let handlers = awkernel_lib::interrupt::get_handlers();

    console::print("IRQ Name\r\n");
    for (k, v) in handlers.iter() {
        let msg = format!("{:>3} name: {}\r\n", k, v);
        console::print(&msg);
    }
}

#[embedded]
fn ifconfig_ffi() {
    let ifs = awkernel_lib::net::get_interfaces();
    for netif in ifs.iter() {
        let msg = format!("{netif}\r\n\r\n");
        console::print(&msg);
    }
}

// #[embedded]
// fn udptest_ffi() {
//     console::print("Testing UDP\r\n");
//     udp::udp_test();
// }

fn print_tasks() {
    let tasks = task::get_tasks();

    console::print("Tasks:\r\n");

    let msg = format!(
        "{:>5} {:<10} {:<8} {:>14} {:>14} name\r\n",
        "ID", "State", "In Queue", "#Preemption", "Last Executed"
    );
    console::print(&msg);

    for t in tasks {
        let mut node = MCSNode::new();
        let info = t.info.lock(&mut node);

        let state = format!("{:?}", info.get_state());

        let msg = format!(
            "{:>5} {:<10} {:<8} {:>14} {:>14} {}\r\n",
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
