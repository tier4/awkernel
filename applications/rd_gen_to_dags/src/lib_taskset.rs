#![no_std]
extern crate alloc;

mod build_dag;
mod parse_yaml;
mod time_unit;

use alloc::string::ToString;
use alloc::vec;
use alloc::vec::Vec;
use awkernel_async_lib::{
    dag::{finish_create_dags, reset_all_dags}, 
    pubsub::reset_pubsub,
    scheduler::SchedulerType, 
    sleep,
    task::{get_tasks, set_need_terminate, whether_dag, perf::{reset_perf_logs}}
};
use awkernel_lib::{console, sync::mutex::MCSNode};
use build_dag::build_dag;
use core::time::Duration;

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
// const DAG_FILE_0: &str = concat!(include_str!("path/to/dag_0.yaml"), "\n");
// const DAG_FILE_1: &str = concat!(include_str!("path/to/dag_1.yaml"), "\n");

/// If no specific scheduler feature is enabled, it defaults to `SchedulerType::PrioritizedFIFO(0)`.
/// Only schedulers for DAGs can be defined here.
fn get_configured_scheduler_type() -> SchedulerType {
    // SchedulerType::PrioritizedFIFOFORDAG(0)
    SchedulerType::GEDF(0)
    // SchedulerType::PrioritizedRR(2)
}

/// Read a command or number input from console (supports 1-2 digit input or "task")
async fn read_input_number() -> u8 {
    let mut input = alloc::string::String::new();
    let mut ignore_lf = false;

    loop {
        if let Some(c) = console::get() {
            if ignore_lf {
                ignore_lf = false;
                if c == b'\n' {
                    continue;
                }
            }

            match c {
                b'\r' | b'\n' => {
                    // Enter pressed - parse the input
                    if c == b'\r' {
                        ignore_lf = true;
                    }

                    console::put(b'\r');
                    console::put(b'\n');

                    let trimmed = input.trim().to_string();
                    if trimmed.is_empty() {
                        console::print("Invalid input. Please enter a number (0-18) or 'task'.\r\n");
                        console::print("> ");
                        continue;
                    }

                    if trimmed == "task" {
                        print_tasks();
                        console::print("\r\n> ");
                        input.clear();
                        continue;
                    }

                    // Try to parse the input as u8
                    let mut num: u8 = 0;
                    for ch in trimmed.chars() {
                        if let Some(digit) = ch.to_digit(10) {
                            num = num * 10 + digit as u8;
                        } else {
                            console::print("Invalid input. Please enter a number (0-18) or 'task'.\r\n");
                            console::print("> ");
                            input.clear();
                            num = 0;
                            break;
                        }
                    }

                    if trimmed.chars().any(|ch| !ch.is_ascii_digit()) {
                        continue;
                    }

                    // Validate range
                    if num <= 18 {
                        return num;
                    }

                    console::print("Invalid input. Please enter a number (0-18) or 'task'.\r\n");
                    console::print("> ");
                    input.clear();
                }
                0x08 | 0x7F => {
                    // Backspace/delete
                    if !input.is_empty() {
                        input.pop();
                        console::put(0x08);
                        console::put(b' ');
                        console::put(0x08);
                    }
                }
                b'0'..=b'9' | b'a'..=b'z' | b'A'..=b'Z' => {
                    // Allow digits or letters for simple commands (limit length)
                    if input.len() < 8 {
                        input.push(c as char);
                        console::put(c);
                    }
                }
                _ => {
                    // Ignore other characters
                }
            }
        }
        sleep(Duration::from_millis(10)).await;
    }
}

fn print_tasks() {
    let tasks = get_tasks()
        .into_iter()
        .filter(|rt| whether_dag(rt))
        .collect::<Vec<_>>();

    if tasks.is_empty() {
        console::print("No DAG tasks.\r\n");
        return;
    }

    console::print("DAG Tasks:\r\n");

    let msg = alloc::format!(
        "{:>5}  {:<10} {:>14} {:>14} name\r\n",
        "ID", "State", "#Preemption", "Last Executed"
    );
    console::print(&msg);

    for t in tasks {
        let mut node = MCSNode::new();
        let info = t.info.lock(&mut node);

        let state = alloc::format!("{:?}", info.get_state());

        let msg = alloc::format!(
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

/// Print menu and wait for user selection
async fn select_dag_set() -> u8 {
    console::print("\n========================================\r\n");
    console::print("Select DAG Set:\r\n");
    console::print("  1: DAG Set 1 (TU=1.0) \r\n");
    console::print("  2: DAG Set 2 (TU=1.5)\r\n");
    console::print("  3: DAG Set 3 (TU=1.5)\r\n");
    console::print("  4: DAG Set 4 (TU=1.5)\r\n");
    console::print("  5: DAG Set 5 (TU=1.5)\r\n");
    console::print("  6: DAG Set 6 (TU=1.5)\r\n");
    console::print("  7: DAG Set 7 (TU=2.0)\r\n");
    console::print("  8: DAG Set 8 (TU=2.0)\r\n");
    console::print("  9: DAG Set 9 (TU=2.0)\r\n");
    console::print(" 10: DAG Set 10 (TU=2.0)\r\n");
    console::print(" 11: DAG Set 11 (TU=2.0)\r\n");
    console::print(" 12: DAG Set 12 (TU=2.5)\r\n");
    console::print(" 13: DAG Set 13 (TU=2.5)\r\n");
    console::print(" 14: DAG Set 14 (TU=2.5)\r\n");
    console::print(" 15: DAG Set 15 (TU=2.5)\r\n");
    console::print(" 16: DAG Set 16 (TU=2.5)\r\n");
    console::print(" 17: DAG Set 17 (TU=3.0)\r\n");
    console::print(" 18: DAG Set 18 (TU=3.0)\r\n");
    console::print("  0: Reset (terminate tasks, not yet.)\r\n");
    console::print("========================================\r\n");
    console::print("> ");
    
    read_input_number().await
}

/// Spawn DAGs from the selected set
async fn spawn_dag_set(choice: u8) -> bool {
    let dag_files = match choice {
        1 => [DAG_FILE_0_04, DAG_FILE_0_03, DAG_FILE_1_03].as_slice(),
        2 => [DAG_FILE_0_05, DAG_FILE_1_05, DAG_FILE_2_05].as_slice(),
        3 => [DAG_FILE_0_05, DAG_FILE_3_05, DAG_FILE_4_05].as_slice(),
        4 => [DAG_FILE_0_05, DAG_FILE_5_05, DAG_FILE_6_05].as_slice(),
        5 => [DAG_FILE_0_05, DAG_FILE_1_05, DAG_FILE_3_05].as_slice(),
        6 => [DAG_FILE_0_05, DAG_FILE_1_05, DAG_FILE_4_05].as_slice(),
        7 => [DAG_FILE_0_10, DAG_FILE_0_05, DAG_FILE_1_05].as_slice(),
        8 => [DAG_FILE_0_10, DAG_FILE_2_05, DAG_FILE_3_05].as_slice(),
        9 => [DAG_FILE_0_10, DAG_FILE_4_05, DAG_FILE_5_05].as_slice(),
        10 => [DAG_FILE_0_10, DAG_FILE_0_05, DAG_FILE_6_05].as_slice(),
        11 => [DAG_FILE_0_10, DAG_FILE_1_05, DAG_FILE_2_05].as_slice(),
        12 => [DAG_FILE_0_10, DAG_FILE_1_10, DAG_FILE_0_05].as_slice(),
        13 => [DAG_FILE_0_10, DAG_FILE_2_10, DAG_FILE_1_05].as_slice(),
        14 => [DAG_FILE_0_10, DAG_FILE_3_10, DAG_FILE_2_05].as_slice(),
        15 => [DAG_FILE_0_10, DAG_FILE_4_10, DAG_FILE_3_05].as_slice(),
        16 => [DAG_FILE_0_10, DAG_FILE_5_10, DAG_FILE_4_05].as_slice(),
        17 => [DAG_FILE_0_10, DAG_FILE_1_10, DAG_FILE_2_10].as_slice(),
        18 => [DAG_FILE_0_10, DAG_FILE_3_10, DAG_FILE_4_10].as_slice(),
        _ => {
            log::error!("Invalid choice: {}", choice);
            return false;
        }
    };

    let dags_data = match parse_yaml::parse_dags(dag_files) {
        Ok(data) => data,
        Err(e) => {
            log::error!("Failed to parse YAML: {e}");
            return false;
        }
    };

    let mut success_build_dags = vec![];
    let sched_type = get_configured_scheduler_type();

    for dag_data in dags_data {
        match build_dag(dag_data, sched_type).await {
            Ok(dag) => {
                success_build_dags.push(dag);
            }
            Err(e) => {
                log::error!("Failed to build DAG: {e}");
            }
        }
    }

    if success_build_dags.is_empty() {
        log::error!("Failed to build DAG");
        return false;
    }

    match finish_create_dags(&success_build_dags).await {
        Ok(_) => {
            log::info!("DAG Set {} created successfully.", choice);
            true
        }
        Err(errors) => {
            log::error!("Failed to create DAGs");
            for error in errors {
                log::error!("- {error}");
            }
            false
        }
    }
}

async fn wait_for_dag_termination() {
    loop {
        let remaining = get_tasks()
            .into_iter()
            .filter(|rt| whether_dag(rt))
            .count();
        if remaining == 0 {
            break;
        }
        sleep(Duration::from_millis(10)).await;
    }
}

// const DAG_FILE_0: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/custom/dag_node2.yaml"), "\n");
// const DAG_FILE_1: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/custom/dag_pub6.yaml"), "\n");
// const DAG_FILE_0: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=2/DAGs/dag_0.yaml"), "\n");
// TU=0.3
const DAG_FILE_0_03: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.3/DAGs/dag_0.yaml"), "\n");
const DAG_FILE_1_03: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.3/DAGs/dag_3.yaml"), "\n");
// TU=0.4
const DAG_FILE_0_04: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.4/DAGs/dag_0.yaml"), "\n");
// TU=0.5
const DAG_FILE_0_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_0.yaml"), "\n");
const DAG_FILE_1_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_7.yaml"), "\n");
const DAG_FILE_2_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_8.yaml"), "\n");
const DAG_FILE_3_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_9.yaml"), "\n");
const DAG_FILE_4_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_10.yaml"), "\n");
const DAG_FILE_5_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_17.yaml"), "\n");
const DAG_FILE_6_05: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=0.5/DAGs/dag_19.yaml"), "\n");
// TU=1.0
const DAG_FILE_0_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_0.yaml"), "\n");
const DAG_FILE_1_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_2.yaml"), "\n");
const DAG_FILE_2_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_3.yaml"), "\n");
const DAG_FILE_3_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_7.yaml"), "\n");
const DAG_FILE_4_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_11.yaml"), "\n");
const DAG_FILE_5_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_16.yaml"), "\n");
const DAG_FILE_6_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_18.yaml"), "\n");
const DAG_FILE_7_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_22.yaml"), "\n");
const DAG_FILE_8_10: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_23.yaml"), "\n");
// const DAG_FILE_3: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/DAGs/DAGs/dag_3.yaml"), "\n");
// const DAG_FILE_1: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/DAGs/dag1_eva.yaml"), "\n");
// const DAG_FILE_2: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/DAGs/dag2_eva.yaml"), "\n");
// const DAG_FILE_3: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/DAGs/dag3_eva.yaml"), "\n");
// const DAG_FILE_4: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/DAGs/dag4_eva.yaml"), "\n");
// const DAG_FILE_5: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/DAGs/dag5_eva.yaml"), "\n");

pub async fn run() {
    sleep(Duration::from_millis(1000)).await;

    loop {
        // Wait for standard input and get user selection
        let choice = select_dag_set().await;

        match choice {
            1..=18 => {
                // Record measurement start time (from when input was received)
                log::info!("Starting measurement for DAG Set {}...", choice);
                
                if spawn_dag_set(choice).await {
                    log::info!("DAG Set {} spawned and measurement started.", choice);
                } else {
                    console::print("Failed to spawn DAG set. Please try again.\r\n");
                }
            }
            0 => {
                let tasks = get_tasks()
                    .into_iter()
                    .filter(|rt| whether_dag(rt) == true) // Filter out idle CPUs
                    .collect::<Vec<_>>();
                for task in tasks {
                    set_need_terminate(task.id);
                }


                log::info!("Resetting tasks...");
                wait_for_dag_termination().await;
                reset_pubsub();
                reset_perf_logs();
                reset_all_dags();
            }
            _ => {
                console::print("Invalid choice. Please select 0-18.\r\n");
            }
        }
    }
}
