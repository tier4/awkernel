#![no_std]

use awkernel_async_lib::dag::graph::Graph;
use awkernel_lib::delay::wait_microsec;

pub async fn run() {
    wait_microsec(1000000);

    let mut graph: Graph<&str, &str> = Graph::new();

    let a = graph.add_node("A");
    let b = graph.add_node("B");
    let c = graph.add_node("C");

    let ab = graph.add_edge(a, b, "A-B");
    let _ac = graph.add_edge(a, c, "A-C");
    let _bc = graph.add_edge(b, c, "B-C");

    log::info!("Graph: {:#?}", graph);

    if let Some((src, tdt)) = graph.edge_endpoints(ab) {
        log::info!("Edge ab: {:?} -> {:?}", src, tdt);
    }

    graph.remove_node(c);
    log::info!("Graph: {:#?}", graph);
}
