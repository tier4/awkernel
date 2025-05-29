mod graph;
mod unionfind;
mod visit;

use crate::{
    dag::graph::{
        algo::{connected_components, is_cyclic_directed},
        NodeIndex,
    },
    scheduler::SchedulerType,
    spawn_reactor, spawn_sink_reactor, MultipleReceiver, MultipleSender, VectorToPublishers,
    VectorToSubscribers,
};

#[cfg(feature = "perf")]
use crate::spawn_periodic_reactor_with_measure;
#[cfg(feature = "perf")]
use awkernel_lib::delay::cpu_counter;

#[cfg(not(feature = "perf"))]
use crate::spawn_periodic_reactor;

use alloc::{
    borrow::Cow,
    boxed::Box,
    collections::{btree_map, BTreeMap},
    sync::Arc,
    vec::Vec,
};
use awkernel_lib::sync::mutex::{MCSNode, Mutex};
use core::{future::Future, pin::Pin, time::Duration};

static DAGS: Mutex<Dags> = Mutex::new(Dags::new()); // Set of DAGs.
static PENDING_TASKS: Mutex<BTreeMap<u32, Vec<PendingTask>>> = Mutex::new(BTreeMap::new()); // key: dag_id

#[cfg(feature = "perf")]
static SOURCE_PENDING_TASKS: Mutex<BTreeMap<u32, Vec<PendingTask>>> = Mutex::new(BTreeMap::new()); // key: dag_id

pub enum DagError {
    NotWeaklyConnected(u32),
    ContainsCycle(u32),
    MissingPendingTasks(u32),
}

struct PendingTask {
    node_idx: NodeIndex,
    spawn: Box<dyn FnOnce() -> Pin<Box<dyn Future<Output = u32> + Send>> + Send>,
}

impl PendingTask {
    fn new<F>(node_idx: NodeIndex, spawn_fn: F) -> Self
    where
        F: FnOnce() -> Pin<Box<dyn Future<Output = u32> + Send>> + Send + 'static,
    {
        Self {
            node_idx,
            spawn: Box::new(spawn_fn),
        }
    }
}

struct NodeInfo {
    task_id: u32,
    subscribe_topics: Vec<Cow<'static, str>>,
    publish_topics: Vec<Cow<'static, str>>,
    relative_deadline: Option<Duration>,
}

#[cfg(feature = "perf")]
struct ResponseInfo {
    release_time: BTreeMap<NodeIndex, Vec<u64>>,
    response_time: Vec<u64>,
}

#[cfg(feature = "perf")]
impl ResponseInfo {
    fn new() -> Self {
        Self {
            release_time: BTreeMap::new(),
            response_time: Vec::new(),
        }
    }

    fn get_release_time_at(&self, at_idx: usize) -> Option<u64> {
        let mut earliest_release_time = u64::MAX;

        for (_, release_times) in self.release_time.iter() {
            if let Some(&release_time) = release_times.get(at_idx) {
                if release_time < earliest_release_time {
                    earliest_release_time = release_time;
                }
            }
        }
        if earliest_release_time == u64::MAX {
            None
        } else {
            Some(earliest_release_time)
        }
    }

    fn add_release_time(&mut self, node_idx: NodeIndex, current_time: u64) {
        self.release_time
            .entry(node_idx)
            .or_default()
            .push(current_time);
    }

    fn add_response_time(&mut self, finish_time: u64) {
        let release_time = self
            .get_release_time_at(self.response_time.len())
            .expect("release_time is always recorded due to precedence constraints.");

        self.response_time.push(finish_time - release_time);
    }
}

pub struct Dag {
    id: u32,
    graph: Mutex<graph::Graph<NodeInfo, u32>>, //TODO: Change to edge attribute

    #[cfg(feature = "perf")]
    response_info: Mutex<ResponseInfo>,
}

impl Dag {
    pub fn get_id(&self) -> u32 {
        self.id
    }

    pub fn node_count(&self) -> usize {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.node_count()
    }

    pub fn edge_count(&self) -> usize {
        let mut node = MCSNode::new();
        let graph = self.graph.lock(&mut node);
        graph.edge_count()
    }

    fn add_node_with_topic_edges(
        &self,
        subscribe_topic_names: &[Cow<'static, str>],
        publish_topic_names: &[Cow<'static, str>],
    ) -> NodeIndex {
        let add_node_info = NodeInfo {
            task_id: 0, // Temporary task_id
            subscribe_topics: subscribe_topic_names.to_vec(),
            publish_topics: publish_topic_names.to_vec(),
            relative_deadline: None,
        };

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);
        let add_node_idx = graph.add_node(add_node_info);

        for node_idx in graph.node_indices() {
            if let Some(node_info) = graph.node_weight(node_idx) {
                let subscribe_match = subscribe_topic_names
                    .iter()
                    .any(|sub| node_info.publish_topics.contains(sub));

                let publish_match = publish_topic_names
                    .iter()
                    .any(|pub_| node_info.subscribe_topics.contains(pub_));

                if subscribe_match {
                    graph.add_edge(node_idx, add_node_idx, 0);
                }

                if publish_match {
                    graph.add_edge(add_node_idx, node_idx, 0);
                }
            }
        }

        add_node_idx
    }

    pub async fn register_reactor<F, Args, Ret>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        subscribe_topic_names: Vec<Cow<'static, str>>,
        publish_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
    ) where
        F: Fn(
                <Args::Subscribers as MultipleReceiver>::Item,
            ) -> <Ret::Publishers as MultipleSender>::Item
            + Send
            + 'static,
        Args: VectorToSubscribers,
        Ret: VectorToPublishers,
        Ret::Publishers: Send,
        Args::Subscribers: Send,
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &publish_topic_names);

        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);

        pending_tasks
            .entry(self.id)
            .or_default()
            .push(PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_reactor::<F, Args, Ret>(
                        reactor_name.clone(),
                        f,
                        subscribe_topic_names.clone(),
                        publish_topic_names.clone(),
                        sched_type,
                    )
                    .await
                })
            }));
    }

    pub async fn register_periodic_reactor<F, Ret>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        publish_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
        period: Duration,
    ) where
        F: Fn() -> <Ret::Publishers as MultipleSender>::Item + Send + 'static,
        Ret: VectorToPublishers,
        Ret::Publishers: Send,
    {
        let node_idx = self.add_node_with_topic_edges(&Vec::new(), &publish_topic_names);

        #[cfg(feature = "perf")]
        {
            let mut node = MCSNode::new();
            let mut source_pending_tasks = SOURCE_PENDING_TASKS.lock(&mut node);

            let dag_id = self.id;

            let measure_f = move || {
                let release_time = cpu_counter();
                let dag = get_dag(dag_id).unwrap();
                let mut node = MCSNode::new();
                let mut response_info = dag.response_info.lock(&mut node);
                response_info.add_release_time(node_idx, release_time);
            };

            source_pending_tasks
                .entry(self.id)
                .or_default()
                .push(PendingTask::new(node_idx, move || {
                    Box::pin(async move {
                        spawn_periodic_reactor_with_measure::<_, Ret, _>(
                            reactor_name.clone(),
                            f,
                            publish_topic_names.clone(),
                            sched_type,
                            period,
                            measure_f,
                        )
                        .await
                    })
                }));
        }

        #[cfg(not(feature = "perf"))]
        {
            let mut node = MCSNode::new();
            let mut pending_tasks = PENDING_TASKS.lock(&mut node);
            pending_tasks
                .entry(self.id)
                .or_default()
                .push(PendingTask::new(node_idx, move || {
                    Box::pin(async move {
                        spawn_periodic_reactor::<F, Ret>(
                            reactor_name.clone(),
                            f,
                            publish_topic_names.clone(),
                            sched_type,
                            period,
                        )
                        .await
                    })
                }));
        }
    }

    pub async fn register_sink_reactor<F, Args>(
        &self,
        reactor_name: Cow<'static, str>,
        f: F,
        subscribe_topic_names: Vec<Cow<'static, str>>,
        sched_type: SchedulerType,
        relative_deadline: Duration,
    ) where
        F: Fn(<Args::Subscribers as MultipleReceiver>::Item) + Send + 'static,
        Args: VectorToSubscribers,
        Args::Subscribers: Send,
    {
        let node_idx = self.add_node_with_topic_edges(&subscribe_topic_names, &Vec::new());

        let mut node = MCSNode::new();
        let mut graph = self.graph.lock(&mut node);

        graph.node_weight_mut(node_idx).unwrap().relative_deadline = Some(relative_deadline);

        let mut node = MCSNode::new();
        let mut pending_tasks = PENDING_TASKS.lock(&mut node);

        #[cfg(feature = "perf")]
        {
            let dag_id = self.id;

            let wrapped_f = move |arg: <Args::Subscribers as MultipleReceiver>::Item| {
                f(arg);

                {
                    let finish_time = cpu_counter();
                    let dag = get_dag(dag_id).unwrap();
                    let mut node = MCSNode::new();
                    let mut response_info = dag.response_info.lock(&mut node);
                    response_info.add_response_time(finish_time);
                }
            };

            pending_tasks
                .entry(self.id)
                .or_default()
                .push(PendingTask::new(node_idx, move || {
                    Box::pin(async move {
                        spawn_sink_reactor::<_, Args>(
                            reactor_name.clone(),
                            wrapped_f,
                            subscribe_topic_names.clone(),
                            sched_type,
                        )
                        .await
                    })
                }));
        }

        #[cfg(not(feature = "perf"))]
        pending_tasks
            .entry(self.id)
            .or_default()
            .push(PendingTask::new(node_idx, move || {
                Box::pin(async move {
                    spawn_sink_reactor::<F, Args>(
                        reactor_name.clone(),
                        f,
                        subscribe_topic_names.clone(),
                        sched_type,
                    )
                    .await
                })
            }));
    }
}

/// DAGs.
struct Dags {
    candidate_id: u32, // Next candidate of Dag ID.
    id_to_dag: BTreeMap<u32, Arc<Dag>>,
}

impl Dags {
    const fn new() -> Self {
        Self {
            candidate_id: 1,
            id_to_dag: BTreeMap::new(),
        }
    }

    fn create(&mut self) -> Arc<Dag> {
        let mut id = self.candidate_id;
        loop {
            // Find an unused DAG ID.
            if let btree_map::Entry::Vacant(e) = self.id_to_dag.entry(id) {
                let dag = Arc::new(Dag {
                    id,
                    graph: Mutex::new(graph::Graph::new()),

                    #[cfg(feature = "perf")]
                    response_info: Mutex::new(ResponseInfo::new()),
                });

                e.insert(dag.clone());
                self.candidate_id = id;

                return dag;
            } else {
                // The candidate DAG ID is already used.
                // Check next candidate.
                // If it overflows, start from 1.
                id = id.wrapping_add(1).max(1);
            }
        }
    }
}

pub fn create_dag() -> Arc<Dag> {
    let mut node = MCSNode::new();
    let mut dags = DAGS.lock(&mut node);
    dags.create()
}

pub fn get_dag(id: u32) -> Option<Arc<Dag>> {
    let mut node = MCSNode::new();
    let dags = DAGS.lock(&mut node);
    dags.id_to_dag.get(&id).cloned()
}

fn validate_dag(dag: &Dag) -> Result<(), DagError> {
    let mut pending_node = MCSNode::new();
    if PENDING_TASKS.lock(&mut pending_node).get(&dag.id).is_none() {
        return Err(DagError::MissingPendingTasks(dag.id));
    }

    let mut graph_node = MCSNode::new();
    let graph = dag.graph.lock(&mut graph_node);
    if connected_components(&*graph) != 1 {
        return Err(DagError::NotWeaklyConnected(dag.id));
    }
    if is_cyclic_directed(&*graph) {
        return Err(DagError::ContainsCycle(dag.id));
    }
    Ok(())
}

pub async fn finish_create_dags(dags: &[Arc<Dag>]) -> Result<(), DagError> {
    for dag in dags {
        validate_dag(dag)?;

        let pending_tasks = {
            let mut node = MCSNode::new();
            let mut lock = PENDING_TASKS.lock(&mut node);
            lock.remove(&dag.id).unwrap()
        };

        for task in pending_tasks {
            let task_id = (task.spawn)().await;
            let mut graph_node = MCSNode::new();
            let mut graph = dag.graph.lock(&mut graph_node);
            if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
                node_info.task_id = task_id;
            }
        }

        // Data published before successor nodes were ready was lost, leading to
        // publish/receive count mismatches and inaccurate response time calculations.
        // To prevent this, source nodes now spawn only after all successors are prepared.
        #[cfg(feature = "perf")]
        {
            let source_pending_tasks = {
                let mut node = MCSNode::new();
                let mut lock = SOURCE_PENDING_TASKS.lock(&mut node);
                lock.remove(&dag.id).unwrap_or_default()
            };

            for task in source_pending_tasks {
                let task_id = (task.spawn)().await;
                let mut graph_node = MCSNode::new();
                let mut graph = dag.graph.lock(&mut graph_node);
                if let Some(node_info) = graph.node_weight_mut(task.node_idx) {
                    node_info.task_id = task_id;
                }
            }
        }
    }

    Ok(())
}
