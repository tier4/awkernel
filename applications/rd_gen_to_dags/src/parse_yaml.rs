use alloc::{collections::BTreeMap, string::String, string::ToString, vec::Vec};
use serde::Deserialize;
use yaml_peg::serde::from_str;

// TODO: Remove allow(dead_code).
#[allow(dead_code)]
#[derive(Debug)]
pub(super) enum ParseError {
    EmptyYaml,
    UnmatchedYaml(String),
    MultipleDocumentsFound,
}

#[derive(Deserialize, Debug)]
struct RawNode {
    end_to_end_deadline: Option<u64>,
    execution_time: u64,
    id: u32,
    period: Option<u64>,
}

#[derive(Deserialize, Debug)]
struct RawLink {
    source: u32,
    target: u32,
}

#[derive(Deserialize, Debug)]
struct RawData {
    links: Vec<RawLink>,
    nodes: Vec<RawNode>,
}

#[derive(Debug)]
pub(super) struct NodeData {
    execution_time: u64,
    id: u32,
    period: Option<u64>,
    end_to_end_deadline: Option<u64>,
    out_links: Vec<u32>,
    in_links: Vec<u32>,
}

impl NodeData {
    pub(super) fn get_id(&self) -> u32 {
        self.id
    }

    pub(super) fn get_execution_time(&self) -> u64 {
        self.execution_time
    }

    pub(super) fn get_period(&self) -> Option<u64> {
        self.period
    }

    pub(super) fn get_out_links(&self) -> &[u32] {
        &self.out_links
    }

    pub(super) fn get_in_links(&self) -> &[u32] {
        &self.in_links
    }

    pub(super) fn get_end_to_end_deadline(&self) -> Option<u64> {
        self.end_to_end_deadline
    }

    pub(crate) fn is_source(&self) -> bool {
        self.in_links.is_empty() && !self.out_links.is_empty() && self.period.is_some()
    }

    pub(crate) fn is_sink(&self) -> bool {
        self.out_links.is_empty() && !self.in_links.is_empty() && self.end_to_end_deadline.is_some()
    }
}

#[derive(Debug)]
pub(super) struct DagData {
    nodes: Vec<NodeData>,
}

impl DagData {
    pub(super) fn get_nodes(&self) -> &[NodeData] {
        &self.nodes
    }
}

fn convert_to_dag(raw_data: RawData) -> DagData {
    let mut nodes_map: BTreeMap<u32, NodeData> = raw_data
        .nodes
        .into_iter()
        .map(|raw_node| {
            (
                raw_node.id,
                NodeData {
                    id: raw_node.id,
                    execution_time: raw_node.execution_time,
                    period: raw_node.period,
                    end_to_end_deadline: raw_node.end_to_end_deadline,
                    out_links: Vec::new(),
                    in_links: Vec::new(),
                },
            )
        })
        .collect();

    for raw_link in raw_data.links.iter() {
        if let Some(node) = nodes_map.get_mut(&raw_link.source) {
            node.out_links.push(raw_link.target);
        }
        if let Some(node) = nodes_map.get_mut(&raw_link.target) {
            node.in_links.push(raw_link.source);
        }
    }

    let nodes: Vec<NodeData> = nodes_map.into_values().collect();
    DagData { nodes }
}

// TODO: Remove allow(dead_code).
#[allow(dead_code)]
pub(super) fn parse_dags(dag_files: &[&str]) -> Result<Vec<DagData>, ParseError> {
    dag_files
        .iter()
        .map(|&dag_file| {
            let raw_data_vec: Vec<RawData> =
                from_str(dag_file).map_err(|e| ParseError::UnmatchedYaml(e.to_string()))?;
            match raw_data_vec.len() {
                0 => Err(ParseError::EmptyYaml),
                1 => Ok(convert_to_dag(raw_data_vec.into_iter().next().unwrap())),
                _ => Err(ParseError::MultipleDocumentsFound),
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::vec;

    #[test]
    fn test_parse_dag() {
        let dag_file = "links:
  - source: 0
    target: 1
nodes:
  - execution_time: 10
    id: 0
    period: 50
  - end_to_end_deadline: 40
    execution_time: 20
    id: 1
";
        let result = parse_dags(&[dag_file]);
        assert!(result.is_ok());
        let dags = result.unwrap();
        assert_eq!(dags.len(), 1);
        let dag = &dags[0];
        assert_eq!(dag.nodes.len(), 2);
        assert_eq!(dag.nodes[0].end_to_end_deadline, None);
        assert_eq!(dag.nodes[0].id, 0);
        assert_eq!(dag.nodes[0].execution_time, 10);
        assert_eq!(dag.nodes[0].period, Some(50));
        assert_eq!(dag.nodes[0].out_links, vec![1]);
        assert_eq!(dag.nodes[0].in_links, vec![]);

        assert_eq!(dag.nodes[1].end_to_end_deadline, Some(40));
        assert_eq!(dag.nodes[1].id, 1);
        assert_eq!(dag.nodes[1].execution_time, 20);
        assert_eq!(dag.nodes[1].period, None);
        assert_eq!(dag.nodes[1].out_links, vec![]);
        assert_eq!(dag.nodes[1].in_links, vec![0]);
    }
}
