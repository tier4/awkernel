use alloc::{collections::BTreeMap, vec::Vec};
use serde::Deserialize;
use yaml_peg::serde::from_str;

#[derive(Debug)]
pub(super) enum ParseError {
    EmptyYaml,
    UnmatchedYaml,
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
    pub(super) fn get_execution_time(&self) -> u64 {
        self.execution_time
    }
    pub(super) fn get_id(&self) -> u32 {
        self.id
    }
    pub(super) fn get_period(&self) -> Option<u64> {
        self.period
    }
    pub(super) fn get_end_to_end_deadline(&self) -> Option<u64> {
        self.end_to_end_deadline
    }
    pub(super) fn get_out_links(&self) -> &Vec<u32> {
        &self.out_links
    }
    pub(super) fn get_in_links(&self) -> &Vec<u32> {
        &self.in_links
    }
}

#[derive(Debug)]
pub(super) struct NodesData {
    nodes: Vec<NodeData>,
}

impl NodesData {
    pub(super) fn get_nodes(&self) -> &Vec<NodeData> {
        &self.nodes
    }
}

fn process_raw_data(raw_data: RawData) -> NodesData {
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
    NodesData { nodes }
}

pub(super) fn parse_dag(dag_files: &[&str]) -> Result<Vec<NodesData>, ParseError> {
    dag_files
        .iter()
        .map(|&dag_file| {
            let raw_data_vec: Vec<RawData> =
                from_str(dag_file).map_err(|_| ParseError::UnmatchedYaml)?;
            match raw_data_vec.len() {
                0 => Err(ParseError::EmptyYaml),
                1 => Ok(process_raw_data(raw_data_vec.into_iter().next().unwrap())),
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
        let result = parse_dag(&[dag_file]);
        assert!(result.is_ok());
        let dags = result.unwrap();
        assert_eq!(dags.len(), 1);
        let nodes = dags[0].get_nodes();
        assert_eq!(nodes.len(), 2);

        assert_eq!(nodes[0].get_end_to_end_deadline(), None);
        assert_eq!(nodes[0].get_id(), 0);
        assert_eq!(nodes[0].get_execution_time(), 10);
        assert_eq!(nodes[0].get_period(), Some(50));
        assert_eq!(nodes[0].get_out_links(), &vec![1]);
        assert_eq!(nodes[0].get_in_links(), &vec![]);

        assert_eq!(nodes[1].get_end_to_end_deadline(), Some(40));
        assert_eq!(nodes[1].get_id(), 1);
        assert_eq!(nodes[1].get_execution_time(), 20);
        assert_eq!(nodes[1].get_period(), None);
        assert_eq!(nodes[1].get_out_links(), &vec![]);
        assert_eq!(nodes[1].get_in_links(), &vec![0]);
    }
}
