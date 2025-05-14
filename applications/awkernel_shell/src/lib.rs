#![no_std]

#[macro_use]
extern crate alloc;

use alloc::{
    boxed::Box,
    string::{String, ToString},
    vec::Vec,
};
use awkernel_async_lib::{
    scheduler::SchedulerType,
    sleep,
    task::{self, TaskResult},
};
use awkernel_lib::{console, sync::mutex::MCSNode, IS_STD};
use blisp::{embedded, runtime::FFI};
use core::time::Duration;

const SERVICE_NAME: &str = "[Awkernel] shell";

pub fn init() {
    let task_id = task::spawn(SERVICE_NAME.into(), console_handler(), SchedulerType::FIFO);

    if let Some(irq) = awkernel_lib::console::irq_id() {
        if awkernel_lib::interrupt::register_handler(
            irq,
            "serial port (awkernel_shell)".into(),
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

    #[allow(unused_mut)]
    let mut functions: Vec<Box<dyn FFI + Send>> = vec![
        Box::new(HelpFfi),
        Box::new(TaskFfi),
        Box::new(InterruptFfi),
        Box::new(IfconfigFfi),
    ];

    #[cfg(feature = "perf")]
    functions.push(Box::new(PerfFfi));

    let code = if cfg!(feature = "perf") {
        format!("{CODE}\r\n{PERF_CODE}")
    } else {
        CODE.to_string()
    };

    let exprs = blisp::init(&code, functions).unwrap();
    let blisp_ctx = blisp::typing(exprs).unwrap();

    let mut line = Vec::new();

    console::print("\r\nWelcome to Awkernel!\r\n\r\n");
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
";

const PERF_CODE: &str = "(export perf () (IO (-> () []))
    (perf_ffi))";

#[embedded]
fn help_ffi() {
    console::print("Awkernel v202306\r\n");
    console::print("BLisp grammer: https://ytakano.github.io/blisp/\r\n\r\n");

    console::print("BLisp functions:\r\n");

    let mut lines = String::new();

    lines.push_str("(help)      ; print this message\r\n");
    lines.push_str("(task)      ; print tasks\r\n");
    lines.push_str("(interrupt) ; print interrupt information\r\n");
    lines.push_str("(ifconfig)  ; print network interfaces\r\n");

    #[cfg(feature = "perf")]
    lines.push_str("(perf)      ; print performance information\r\n");

    console::print(lines.as_str());
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
        let msg = format!("{k:>3} name: {v}\r\n");
        console::print(&msg);
    }
}

#[embedded]
fn ifconfig_ffi() {
    let ifs = awkernel_lib::net::get_all_interface();
    for netif in ifs.iter() {
        let msg = format!("{netif}\r\n\r\n");
        console::print(&msg);
    }
}

#[cfg(feature = "perf")]
#[embedded]
fn perf_ffi() {
    console::print("Perform non-primary CPU [tsc]:\r\n");
    console::print(" cpu | Type           |   kernel_time  |    task_time   |    idle_time   | interrupt_time | context_switch |    perf_time   \r\n");
    console::print("=====|================|================|================|================|================|================|================\r\n");

    use awkernel_async_lib::task::perf;

    const F: usize = 2;

    for cpu_id in 0..awkernel_lib::cpu::num_cpu() {
        let kernel_time = perf::get_kernel_time(cpu_id);
        let task_time = perf::get_task_time(cpu_id);
        let idle_time = perf::get_idle_time(cpu_id);
        let interrupt_time = perf::get_interrupt_time(cpu_id);
        let contxt_switch_time = perf::get_context_switch_time(cpu_id);
        let perf_time = perf::get_perf_time(cpu_id);

        let msg = format!(
            "{cpu_id:>4} | Total          |{kernel_time:>15} |{task_time:>15} |{idle_time:>15} |{interrupt_time:>15} |{contxt_switch_time:>15} |{perf_time:>15}\r\n"
        );

        console::print(&msg);

        let ave_kernel_time = perf::get_ave_kernel_time(cpu_id).unwrap_or(0.0);
        let ave_task_time = perf::get_ave_task_time(cpu_id).unwrap_or(0.0);
        let ave_idle_time = perf::get_ave_idle_time(cpu_id).unwrap_or(0.0);
        let ave_interrupt_time = perf::get_ave_interrupt_time(cpu_id).unwrap_or(0.0);
        let ave_contxt_switch_time = perf::get_ave_context_switch_time(cpu_id).unwrap_or(0.0);
        let ave_perf_time = perf::get_ave_perf_time(cpu_id).unwrap_or(0.0);

        let msg_ave = format!(
            "     | Avg            | {ave_kernel_time:>14.F$} | {ave_task_time:>14.F$} |{ave_idle_time:>15.F$} |{ave_interrupt_time:>15.F$} |{ave_contxt_switch_time:>15.F$} |{ave_perf_time:>15.F$}\r\n",
        );

        console::print(&msg_ave);

        let worst_kernel_time = perf::get_kernel_wcet(cpu_id);
        let worst_task_time = perf::get_task_wcet(cpu_id);
        let worst_idle_time = perf::get_idle_wcet(cpu_id);
        let worst_interrupt_time = perf::get_interrupt_wcet(cpu_id);
        let worst_contxt_switch_time = perf::get_context_switch_wcet(cpu_id);
        let worst_perf_time = perf::get_perf_wcet(cpu_id);

        let msg_worst = format!(
            "     | Worst          | {worst_kernel_time:>14} | {worst_task_time:>14} |{worst_idle_time:>15} |{worst_interrupt_time:>15} |{worst_contxt_switch_time:>15} |{worst_perf_time:>15}\r\n",
        );

        console::print(&msg_worst);

        if cpu_id < awkernel_lib::cpu::num_cpu() - 1 {
            console::print("-----|----------------|----------------|----------------|----------------|----------------|----------------|----------------\r\n");
        }
    }
}

fn print_tasks() {
    let tasks = task::get_tasks();

    console::print("Tasks:\r\n");

    let msg = format!(
        "{:>5}  {:<10} {:>14} {:>14} name\r\n",
        "ID", "State", "#Preemption", "Last Executed"
    );
    console::print(&msg);

    for t in tasks {
        let mut node = MCSNode::new();
        let info = t.info.lock(&mut node);

        let state = format!("{:?}", info.get_state());

        let msg = format!(
            "{:>5}{} {:<10} {:>14} {:>14} {}\r\n",
            t.id,
            if info.panicked() { "*" } else { " " },
            state,
            info.get_num_preemption(),
            info.get_last_executed().uptime().as_micros(),
            t.name,
        );

        console::print(&msg);
    }
}
