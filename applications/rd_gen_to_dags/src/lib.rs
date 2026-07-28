#![no_std]
extern crate alloc;

mod build_dag;
mod dag_stats;
mod parse_yaml;
mod time_unit;

use alloc::vec;
use awkernel_async_lib::dag::finish_create_dags;
use awkernel_lib::delay::wait_millisec;
use build_dag::build_dag;

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
const DAG_FILE_0: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=2/DAGs/dag_0.yaml"), "\n");
const DAG_FILE_1: &str = concat!(include_str!("/home/nokosan/azumi-lab/RD-Gen/test/TU=1/DAGs/dag_1.yaml"), "\n");

pub async fn run() {
    wait_millisec(1000);

    let dag_files = [DAG_FILE_0, DAG_FILE_1];

    let dags_data = match parse_yaml::parse_dags(&dag_files) {
        Ok(data) => data,
        Err(e) => {
            log::error!("Failed to parse YAML: {e}");
            return;
        }
    };

    let mut success_build_dags = vec![];

    for dag_data in dags_data {
        match build_dag(dag_data).await {
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
        return;
    }

    match finish_create_dags(&success_build_dags).await {
        Ok(_) => {
            log::info!("DAGs created successfully.");
        }
        Err(errors) => {
            log::error!("Failed to create DAGs");
            for error in errors {
                log::error!("- {error}");
            }
        }
    }
}
