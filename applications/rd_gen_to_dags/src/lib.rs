#![no_std]
extern crate alloc;

mod build_dag;
mod parse_yaml;
mod time_unit;

use alloc::vec;
use awkernel_async_lib::{dag::finish_create_dags, scheduler::SchedulerType};
use awkernel_lib::delay::wait_millisec;
use build_dag::build_dag_structure;

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
// TODO: to be removed after filesystem implementation.
const DAG_FILE_0: &str = concat!(include_str!("../DAGs/dag_0.yaml"), "\n");
// const DAG_FILE_1: &str = concat!(include_str!("../../../../DAGs/dag_1.yaml"), "\n");

pub async fn run() {
    wait_millisec(1000);

    let dag_files = [DAG_FILE_0];

    let dags_data = match parse_yaml::parse_dags(&dag_files) {
        Ok(data) => data,
        Err(e) => {
            log::error!("Error parsing YAML: {e}");
            return;
        }
    };

    let expected_dag_count = dags_data.len();

    let mut success_build_dags = vec![];

    for dag_data in dags_data {
        match build_dag_structure(dag_data, SchedulerType::FIFO).await {
            Ok(dag) => {
                success_build_dags.push(dag);
            }
            Err(e) => {
                log::error!("Failed to build DAG: {e}");
            }
        }
    }

    if success_build_dags.len() != expected_dag_count {
        log::error!("Not all DAGs were built successfully.");
        return;
    }

    match finish_create_dags(&success_build_dags).await {
        Ok(_) => {
            log::info!("DAGs created successfully.");
        }
        Err(e) => {
            log::error!("Failed to create DAGs: {e}");
        }
    }
}
