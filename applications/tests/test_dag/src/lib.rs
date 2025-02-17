#![no_std]

use awkernel_async_lib::dag::create_dag;
use awkernel_async_lib::dag::get_dag;
use awkernel_lib::delay::wait_microsec;

pub async fn run() {
    wait_microsec(1000000);

    let dag_id = create_dag();
    let dag = get_dag(dag_id).unwrap();
    dag.debug_print();

    let a = dag.add_node(1);
    let b = dag.add_node(2);
    let c = dag.add_node(3);

    let ab = dag.add_edge(a, b, 12);
    let _ac = dag.add_edge(a, c, 13);
    let _bc = dag.add_edge(b, c, 23);

    dag.debug_print();

    if let Some((src, tdt)) = dag.edge_endpoints(ab) {
        log::info!("Edge ab: {:?} -> {:?}", src, tdt);
    }

    dag.remove_node(c);
    dag.debug_print();
}
