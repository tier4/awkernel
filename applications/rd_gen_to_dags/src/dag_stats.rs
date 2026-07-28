//! Scheduler-agnostic DAG-level aggregation.
//!
//! Computes per-DAG statistics (total WCET volume and critical-path length)
//! from the fully-known node/edge topology that `parse_yaml::DagData` already
//! holds before any reactor is registered. This does not depend on which
//! `SchedulerType` the DAG will eventually use (ClusteredEDF, GEDF,
//! PrioritizedFIFO, or a future Federated scheduler); it is shared groundwork
//! for all of them.

use crate::parse_yaml::{DagData, NodeData};

use alloc::collections::{BTreeMap, VecDeque};

/// DAG-level aggregates derived from per-node WCET (`execution_time`).
pub(crate) struct DagAggregateStats {
    /// `C`: total WCET volume, i.e. the sum of every node's `execution_time`.
    pub(crate) volume: u64,
    /// `L`: critical-path length, i.e. the WCET sum along the longest
    /// source-to-sink path.
    pub(crate) critical_path: u64,
}

/// Compute [`DagAggregateStats`] for `dag_data` via a topological-order DP:
/// `dp[node] = execution_time[node] + max(dp[pred] for pred in in_links)`,
/// and `critical_path = max(dp[node])` over all nodes.
pub(crate) fn compute_dag_stats(dag_data: &DagData) -> DagAggregateStats {
    let nodes = dag_data.get_nodes();

    let volume: u64 = nodes.iter().map(NodeData::get_execution_time).sum();

    let node_by_id: BTreeMap<u32, &NodeData> =
        nodes.iter().map(|node| (node.get_id(), node)).collect();

    let mut in_degree: BTreeMap<u32, usize> = nodes
        .iter()
        .map(|node| (node.get_id(), node.get_in_links().len()))
        .collect();

    let mut queue: VecDeque<u32> = in_degree
        .iter()
        .filter(|&(_, &degree)| degree == 0)
        .map(|(&id, _)| id)
        .collect();

    let mut dp: BTreeMap<u32, u64> = BTreeMap::new();
    let mut critical_path = 0;

    while let Some(id) = queue.pop_front() {
        let Some(node) = node_by_id.get(&id) else {
            continue;
        };

        let pred_max = node
            .get_in_links()
            .iter()
            .filter_map(|pred_id| dp.get(pred_id).copied())
            .max()
            .unwrap_or(0);
        let finish = pred_max + node.get_execution_time();
        dp.insert(id, finish);
        critical_path = critical_path.max(finish);

        for out_id in node.get_out_links() {
            if let Some(degree) = in_degree.get_mut(out_id) {
                *degree = degree.saturating_sub(1);
                if *degree == 0 {
                    queue.push_back(*out_id);
                }
            }
        }
    }

    DagAggregateStats {
        volume,
        critical_path,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parse_yaml::parse_dags;

    #[test]
    fn test_compute_dag_stats_chain() {
        // 0 --10--> 1 --20--> 2 (linear chain, single path)
        let dag_file = "links:
  - source: 0
    target: 1
  - source: 1
    target: 2
nodes:
  - execution_time: 10
    id: 0
    period: 50
  - execution_time: 20
    id: 1
  - end_to_end_deadline: 40
    execution_time: 5
    id: 2
";
        let dags = parse_dags(&[dag_file]).unwrap();
        let stats = compute_dag_stats(&dags[0]);
        assert_eq!(stats.volume, 35);
        assert_eq!(stats.critical_path, 35);
    }

    #[test]
    fn test_compute_dag_stats_diamond() {
        // 0 fans out to 1 (heavy, 30) and 2 (light, 5); both join at 3.
        // Critical path must follow the heavier branch (0 -> 1 -> 3), not
        // simply sum every node.
        let dag_file = "links:
  - source: 0
    target: 1
  - source: 0
    target: 2
  - source: 1
    target: 3
  - source: 2
    target: 3
nodes:
  - execution_time: 10
    id: 0
    period: 50
  - execution_time: 30
    id: 1
  - execution_time: 5
    id: 2
  - end_to_end_deadline: 100
    execution_time: 5
    id: 3
";
        let dags = parse_dags(&[dag_file]).unwrap();
        let stats = compute_dag_stats(&dags[0]);
        assert_eq!(stats.volume, 50); // 10 + 30 + 5 + 5
        assert_eq!(stats.critical_path, 45); // 10 + 30 + 5, not the 2-fanned sum
    }
}
