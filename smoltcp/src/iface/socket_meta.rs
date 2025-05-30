use super::SocketHandle;
use crate::{
    socket::PollAt,
    time::{Duration, Instant},
    wire::IpAddress,
};
use awkernel_sync::{mcs::MCSNode, mutex::Mutex};

/// Neighbor dependency.
///
/// This enum tracks whether the socket should be polled based on the neighbor
/// it is going to send packets to.
#[derive(Debug, Default, Clone, Copy)]
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub enum NeighborState {
    /// Socket can be polled immediately.
    #[default]
    Active,
    /// Socket should not be polled until either `silent_until` passes or
    /// `neighbor` appears in the neighbor cache.
    Waiting {
        neighbor: IpAddress,
        silent_until: Instant,
    },
}

/// Network socket metadata.
///
/// This includes things that only external (to the socket, that is) code
/// is interested in, but which are more conveniently stored inside the socket
/// itself.
#[cfg_attr(feature = "defmt", derive(defmt::Format))]
pub(crate) struct Meta {
    /// Handle of this socket within its enclosing `SocketSet`.
    /// Mainly useful for debug output.
    pub(crate) handle: Mutex<SocketHandle>,
    /// See [NeighborState](struct.NeighborState.html).
    pub neighbor_state: Mutex<NeighborState>,
}

impl Meta {
    /// Minimum delay between neighbor discovery requests for this particular
    /// socket, in milliseconds.
    ///
    /// See also `iface::NeighborCache::SILENT_TIME`.
    pub(crate) const DISCOVERY_SILENT_TIME: Duration = Duration::from_millis(1_000);

    pub(crate) fn poll_at<F>(&self, socket_poll_at: PollAt, has_neighbor: F) -> PollAt
    where
        F: Fn(IpAddress) -> bool,
    {
        let mut node = MCSNode::new();
        let neighbor_state = self.neighbor_state.lock(&mut node);
        match *neighbor_state {
            NeighborState::Active => socket_poll_at,
            NeighborState::Waiting { neighbor, .. } if has_neighbor(neighbor) => socket_poll_at,
            NeighborState::Waiting { silent_until, .. } => PollAt::Time(silent_until),
        }
    }

    pub(crate) fn egress_permitted<F>(&self, timestamp: Instant, has_neighbor: F) -> bool
    where
        F: Fn(IpAddress) -> bool,
    {
        let mut node = MCSNode::new();
        let neighbor_state = self.neighbor_state.lock(&mut node);
        let neighbor_state_copied = *neighbor_state;
        drop(neighbor_state);

        match neighbor_state_copied {
            NeighborState::Active => true,
            NeighborState::Waiting {
                neighbor,
                silent_until,
            } => {
                if has_neighbor(neighbor) {
                    {
                        let mut node = MCSNode::new();
                        let handle = self.handle.lock(&mut node);
                        net_trace!("{}: neighbor {} discovered, unsilencing", *handle, neighbor);
                    }
                    {
                        let mut node = MCSNode::new();
                        let mut neighbor_state = self.neighbor_state.lock(&mut node);
                        *neighbor_state = NeighborState::Active;
                    }
                    true
                } else if timestamp >= silent_until {
                    let mut node = MCSNode::new();
                    let handle = self.handle.lock(&mut node);
                    net_trace!(
                        "{}: neighbor {} silence timer expired, rediscovering",
                        *handle,
                        neighbor
                    );
                    true
                } else {
                    false
                }
            }
        }
    }

    pub(crate) fn neighbor_missing(&self, timestamp: Instant, neighbor: IpAddress) {
        {
            let mut node = MCSNode::new();
            let handle = self.handle.lock(&mut node);
            net_trace!(
                "{}: neighbor {} missing, silencing until t+{}",
                *handle,
                neighbor,
                Self::DISCOVERY_SILENT_TIME
            );
        }
        {
            let mut node = MCSNode::new();
            let mut neighbor_state = self.neighbor_state.lock(&mut node);
            *neighbor_state = NeighborState::Waiting {
                neighbor,
                silent_until: timestamp + Self::DISCOVERY_SILENT_TIME,
            };
        }
    }
}
