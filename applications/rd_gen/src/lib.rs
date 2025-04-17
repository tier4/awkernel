#![no_std]
extern crate alloc;

mod parse_yaml;

use alloc::vec::Vec;
use awkernel_lib::delay::wait_millisec;
use parse_yaml::{parse_dag, NodesData, ParseError};

// A newline is required at the end due to yaml_peg specification.
// If you have multiple files, define a `const` for each.
// TODO: to be removed after filesystem implementation.
const DAG_FILE_0: &'static str = concat!(include_str!("../../../../DAGs/dag_0.yaml"), "\n");
const DAG_FILE_1: &'static str = concat!(include_str!("../../../../DAGs/dag_1.yaml"), "\n");

// TODO: Implement the remaining DAG construction logic.
async fn process_dags(dags_list: Vec<NodesData>) {
    for dag in dags_list.iter() {
        log::info!("--- Processing new DAG ---");
        for node in dag.get_nodes().iter() {
            log::info!("--- printing node ---");
            log::info!("  Node ID: {}", node.get_id());
            log::info!("  Execution Time: {}", node.get_execution_time());
            if let Some(period) = node.get_period() {
                log::info!("  Period: {}", period);
            }
            if let Some(end_to_end_deadline) = node.get_end_to_end_deadline() {
                log::info!("  End-to-End Deadline: {}", end_to_end_deadline);
            }
            log::info!("  Out Links: {:?}", node.get_out_links());
            log::info!("  In Links: {:?}", node.get_in_links());
        }
    }
}

pub async fn run() {
    wait_millisec(1000);
    // If there are multiple files, specify each one.
    let dag_files = [DAG_FILE_0, DAG_FILE_1];
    match parse_dag(&dag_files) {
        Ok(dags_list) => {
            log::info!("Parsed DAGs successfully.");
            process_dags(dags_list).await;
        }
        Err(e) => match e {
            ParseError::EmptyYaml => log::error!("YAML file is empty."),
            ParseError::UnmatchedYaml => log::error!("YAML format is unmatched."),
            ParseError::MultipleDocumentsFound => {
                log::error!("Multiple documents found in the YAML file.")
            }
        },
    }
}
