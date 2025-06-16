use super::{get_dag, MeasureF};
use alloc::{sync::Arc, vec::Vec};
use awkernel_lib::sync::mutex::MCSNode;
use awkernel_lib::time::Time;
use core::time::Duration;

/// The assumption is that there is one sink vertex and one source vertexe.
pub(super) struct ResponseInfo {
    release_time: Vec<Time>,
    response_time: Vec<Duration>,
}

impl ResponseInfo {
    pub(super) fn new() -> Self {
        Self {
            release_time: Vec::new(),
            response_time: Vec::new(),
        }
    }

    fn add_release_time(&mut self, current_time: Time) {
        self.release_time.push(current_time);
    }

    fn add_response_time(&mut self, response_time: Duration) {
        self.response_time.push(response_time);
    }
}

pub(super) fn create_release_recorder(dag_id: u32) -> MeasureF {
    let closure = move || {
        let release_time = Time::now();
        let dag = get_dag(dag_id).unwrap();
        let mut node = MCSNode::new();
        let mut response_info = dag.response_info.lock(&mut node);
        response_info.add_release_time(release_time);
    };
    Arc::new(closure) as MeasureF
}

pub(super) fn record_response_time(dag_id: u32) {
    let overhead_start = Time::now();

    let dag = get_dag(dag_id).unwrap();
    let mut node = MCSNode::new();
    let mut response_info = dag.response_info.lock(&mut node);

    let release_time = response_info
        .release_time
        .get(response_info.response_time.len())
        .expect("release_time is always recorded due to precedence constraints.");

    let overhead = overhead_start.elapsed();

    let response_time = release_time.elapsed();

    response_info.add_response_time(response_time.saturating_sub(overhead));
}
