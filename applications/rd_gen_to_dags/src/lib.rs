#![no_std]
extern crate alloc;

mod build_dag;
mod parse_yaml;
mod time_unit;

use alloc::vec;
use awkernel_async_lib::{
    dag::{self, finish_create_dags},
    scheduler::SchedulerType,
};
use awkernel_lib::delay::wait_millisec;
use build_dag::build_dag_structure;

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
// TODO: to be removed after filesystem implementation.
const DAG_FILE_0: &str = concat!(include_str!("../DAGs/dag_0.yaml"), "\n");
// const DAG_FILE_1: &str = concat!(include_str!("../../../../DAGs/dag_1.yaml"), "\n");

pub async fn run() {
    wait_millisec(1000);
    log::info!("Starting DAG generation...");
    let dag_files = [DAG_FILE_0];
    let dags_data = parse_yaml::parse_dags(&dag_files);
    match dags_data {
        Ok(dags_data) => {
            log::info!("Creating DAGs...");
            let mut gen_dags = vec![];

            for dag_data in dags_data {
                match build_dag_structure(dag_data, SchedulerType::FIFO).await {
                    Ok(dag) => {
                        gen_dags.push(dag);
                    }
                    Err(e) => {
                        log::error!("Error creating DAG: {e}");
                        continue;
                    }
                }
            }

            let result = finish_create_dags(&gen_dags).await;

            match result {
                Ok(_) => {
                    log::info!("DAG generation completed successfully.");
                }
                Err(_) => {
                    log::error!("Error finishing DAG creation");
                }
            }
        }
        Err(_) => {
            log::error!("Error parsing DAGs");
        }
    }
}
