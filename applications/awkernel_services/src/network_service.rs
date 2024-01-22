use awkernel_async_lib::task::TaskResult;

pub async fn run() -> TaskResult {
    log::info!("Start {}.", crate::NETWORK_SERIVICE_NAME);
    loop {
        // TODO
    }
}
