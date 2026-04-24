# IGC Incremental PR Roadmap

## Summary

- Base branch is `main` at `b9d8b8ce1eeab8c7c10d15106e9dd7887b3c25bb`.
- Treat `igc_fix` as a review stack and rebuild it into small branches with incremental functionality.
- Open pull requests in order. Each branch after the first should be created from the previous roadmap branch so PR `N+1` is reviewed against PR `N`.
- After PR `N` merges, retarget or rebase PR `N+1` onto the updated `main`.
- Ignore merge commit `941d768f837c7480f3d90bae7d3dddbfd571984d` when rebuilding the stack.
- Real-machine validation is required after creating each branch: build with `make x86_64 RELEASE=1`, connect over `/dev/ttyUSB0` at `38400`, reboot from the serial shell, and confirm the target boots the rebuilt kernel via TFTP.

## Current status

### PR2 status

- Branch: `igc_single_queue_polling`
- Commit: `0b1d5c91` (`feat(igc): add single-queue polling datapath`)
- Status: implemented and committed
- Completed scope:
- PCIe endpoint and bridge bus mastering for DMA-capable I225 bring-up
- single-queue TX/RX polling datapath
- `send()`, `recv()`, `can_send()`, and minimal `capabilities()`
- TX reclamation and RX refill for the single-queue path
- Not included:
- `NetDevice::debug_dump`
- shell-side `netdump`
- IRQ RX buffering
- multi-queue support
- TX checksum offload

### Phase 2 review follow-up for PR #683

- Adopted:
- Reworked `igc_txeof()` to reclaim TX descriptors from the descriptor write-back `DD` bit instead of reading `IGC_TDH`.
- Delayed `tx.next_avail_desc` advancement until after the `IGC_TDT` write succeeds, so MMIO write failure cannot leave a zombie software-only descriptor.
- Deferred:
- Kept `send()` returning `Ok(())` on link-down and temporary ring exhaustion to match the existing `igb` / `ixgbe` driver contract used by the current network stack.
- Kept `can_send()` doing reclaim work because the current polling path uses it as a send-readiness gate, and a flag-only check would miss newly freed descriptors.
- Did not add a `RUNNING` check to `igc_recv()` because `igc_stop()` takes the write lock on `inner`, which already serializes teardown against concurrent read-side access.
- Kept `TX_BUFFER_SIZE` at `2048`; PR2 only advertises `VLAN_MTU`, not jumbo-frame TX support, so the current scope remains a minimal single-queue datapath.
- `RX_BUFFER_SIZE` is still sized for jumbo-frame reception; if later commits keep the non-jumbo `VLAN_MTU` scope, shrink it in a follow-up commit as well instead of leaving RX/TX sizing asymmetric.

### Validation completed

- `make clippy`
- `make x86_64 RELEASE=1`
- `make check_x86_64`
- Real-machine smoke test over `/dev/ttyUSB0` at `38400`
- Verified `(reboot)`, return to shell, and `(ifconfig)` interface enumeration
- Remaining gap: full real-traffic TX/RX validation is still pending

### Next task

- Next PR target: `igc_observability`
- Planned contents:
- `NetDevice::debug_dump`
- `awkernel_lib::net::debug_dump_interface`
- shell-side `netdump(interface_id)`
- igc on-demand register and ring dump expansion
- Keep out:
- datapath behavior changes
- IRQ RX buffering
- multi-queue support
- TX checksum offload
- shell write-path helpers such as `add_ipv4`, `arping4`, and `set_gateway4`

## 1. Implementation plan

### PR1: `igc_phy_bringup`

- Source commit: `2e5f21a9` (`fix(igc): stabilize i225 phy bring-up`)
- Goal: stabilize hardware initialization and link bring-up without adding a datapath.
- Include:
- PHY reset retry and timeout handling
- MDIC PHY address synchronization
- power-up before PHY ID reads
- GO_LINKD and ULP clearing before reset
- periodic link polling and link transition logging
- Files expected:
- `awkernel_drivers/src/pcie/intel/igc.rs`
- `awkernel_drivers/src/pcie/intel/igc/i225.rs`
- `awkernel_drivers/src/pcie/intel/igc/igc_phy.rs`
- Review intent: hardware init only, minimal runtime disruption

### PR2: `igc_single_queue_polling`

- Primary source commits: `b582d4ff`, plus the single-queue datapath prerequisites currently mixed into `89650d8b` and `a68d3bf8`
- Goal: first usable single-queue polling TX/RX path
- Include:
- PCI and bridge bus mastering needed for DMA-capable I225 bring-up
- queue-local TX/RX descriptor setup and tail initialization
- `send()`, `recv()`, `can_send()`, `capabilities()` for the minimal polling path
- TX reclamation based on TDH/TDT
- RX consume, refill, and single-queue MRQC configuration
- advanced TX descriptor programming fixes required for actual transmit
- Exclude:
- shell command additions
- `NetDevice::debug_dump` plumbing
- verbose runtime diagnostics beyond cheap bring-up logs
- Files expected:
- `awkernel_drivers/src/pcie.rs`
- `awkernel_drivers/src/pcie/intel/igc.rs`
- `awkernel_drivers/src/pcie/intel/igc/igc_regs.rs`
- Review intent: establish the minimal end-to-end datapath before observability or scaling

### PR3: `igc_observability`

- Source commit material: review and diagnostics pieces split out of `89650d8b`
- Goal: expose cheap observability and operator tooling without changing datapath behavior
- Include:
- `NetDevice::debug_dump` and `debug_dump_interface`
- `netdump` support and the igc register dump hook
- only the shell-side commands that are justified as low-cost debug helpers
- Keep out:
- functional changes to queueing, DMA, or IRQ behavior
- Review intent: on-demand trace hooks, not hot-path instrumentation

### PR4: `igc_irq_rx_buffering`

- Source commit: `f8e151a4` (`fix(igc): buffer rx packets on irq`)
- Goal: decouple RX completion handling from immediate upper-layer consumption
- Include:
- RX packet buffering on IRQ
- matching test adjustments in `applications/tests/test_network`
- Caution:
- Keep `can_send()` as a reclaiming send-readiness gate until interrupt-driven TX reclaim updates the software-visible TX state.
- Only after TX completion reclaim is handled in the IRQ path should `can_send()` be simplified toward a lightweight readiness check.
- `if_net` currently uses `can_send()` as a gate in both polling and IRQ-triggered paths, so simplifying it too early can hide newly freed descriptors.
- Files expected:
- `awkernel_drivers/src/pcie/intel/igc.rs`
- `applications/tests/test_network/src/lib.rs`
- Review intent: preserve single-queue semantics while moving delivery timing

### PR5: `igc_multi_queue`

- Source commit: `14c6239a` (`feat(igc): enable multi-queue tx/rx`)
- Goal: add multi-queue support after the single-queue path is already validated
- Include:
- queue count expansion inside the igc driver
- TX/RX path updates needed to operate on multiple queues
- Keep out:
- generic networking abstraction growth
- new shell or proof-facing interfaces
- Files expected:
- `awkernel_drivers/src/pcie/intel/igc.rs`
- Review intent: isolated scalability step after correctness

### PR6: `igc_tx_csum_offload`

- Source commit: `cabcbe56` (`feat(igc): enable tx checksum offload`)
- Goal: add checksum offload last, after queueing and IRQ behavior are settled
- Include:
- TX checksum descriptor programming
- capability advertisement updates
- `if_net` integration needed to use the capability
- Files expected:
- `awkernel_drivers/src/pcie/intel/igc.rs`
- `awkernel_drivers/src/pcie/intel/igc/igc_base.rs`
- `awkernel_drivers/src/pcie/intel/igc/igc_defines.rs`
- `awkernel_lib/src/net/if_net.rs`
- Review intent: additive performance feature only

## 2. Observable events available now

### already available

- `git log main..igc_fix` already shows a mostly linear feature order suitable for a PR stack.
- PHY reset and link transition diagnostics already exist in the bring-up work and can remain in PR1.
- Existing shell commands such as `ifconfig` are enough to confirm interface enumeration after PR1 and PR2.

### easy to add

- One-line stage markers around PHY init, RX ring init, TX submit, and IRQ RX enqueue
- Counter-style logs for TX completion, RX completion, RX drop, and queue selection
- On-demand register and ring dumps through `debug_dump`

### expensive to add

- Per-descriptor tracing in the hot path
- Detailed interrupt latency instrumentation across all queues
- Persistent packet history buffers in driver memory

### better replaced by a cheaper proxy

- Replace payload logging with ethertype, length, and drop-reason counters
- Replace continuous ring dumps with on-demand shell-triggered snapshots
- Replace proof-facing state exposure with logs and explicit debug hooks

## 3. Interface delta

- PR1 should not change public network interfaces or proof-facing abstractions.
- PR2 should keep queue management and DMA state entirely inside `awkernel_drivers::pcie::intel::igc`.
- PR3 is the main interface expansion point:
- `awkernel_lib::net::NetDevice` gains a read-only debug dump hook
- shell-side observability commands are added only where they directly help hardware bring-up
- PR4 should remain internal to igc plus local test adjustments.
- PR5 should keep multi-queue state driver-local.
- PR6 updates capability signaling in `if_net`, but should stay additive and flag-based.

## 4. Test and trace plan

### Common checks for every PR

- `make x86_64 RELEASE=1`
- wait for the build to finish before rebooting the target
- connect to the target over `/dev/ttyUSB0` with baud rate `38400`
- issue `(reboot)` from the Awkernel serial shell
- confirm the machine TFTP-boots the freshly built kernel
- confirm boot returns to the shell before running branch-specific checks
- `make check_x86_64` if available, otherwise `make check`
- confirm that the diff stays within the intended roadmap slice

### PR1 checks

- validate `igc_phy_bringup` on real hardware immediately after branch creation
- Boot the physical x86_64 target and confirm PHY reset no longer hard-fails
- confirm link-up and link-down logs are emitted correctly

### PR2 checks

- verify interface enumeration
- verify TX submit, RX consume, and descriptor head/tail movement
- confirm the minimal datapath works without relying on IRQ buffering

### PR3 checks

- exercise `netdump` and igc register dump paths from the shell
- confirm observability remains on-demand and does not alter datapath behavior

### PR4 checks

- run the adjusted `applications/tests/test_network`
- confirm IRQ RX buffering does not double-consume descriptors

### PR5 checks

- validate queue initialization and per-queue progress with compact counters
- confirm single-queue behavior remains unchanged when multi-queue is not exercised

### PR6 checks

- verify checksum-offload capability advertisement
- verify checksum-offloaded TX and fallback TX both work correctly

## 5. Risks for the Rocq design

- The largest proof risk is accidental expansion of proof-facing network abstractions. Keep queueing, DMA, and IRQ buffering local to the igc driver.
- `NetDevice` observability hooks in PR3 should be read-only and optional so they do not become semantic dependencies.
- Multi-queue support is the highest runtime and proof-alignment risk. It should ship only after the single-queue path is stable and observable.
- Checksum offload must remain an additive capability, not a redesign of generic packet metadata.
- Do not pull unrelated untracked local files into any roadmap branch.

## Branch creation procedure

- Note: this section reflects the original intended stacked-branch procedure.
- Actual current progress differs:
- PR2 was implemented on `igc_single_queue_polling`
- the current known-good PR2 reference point is `0b1d5c91`
- for PR3, explicitly decide whether to stack on `igc_single_queue_polling` or rebase/reconstruct from updated `main`

1. Create `igc_phy_bringup` from `main`.
2. Cherry-pick or reconstruct the PR1 changes only.
3. Build PR1 with `make x86_64 RELEASE=1`, reboot the physical target over `/dev/ttyUSB0` at `38400`, and confirm the rebuilt kernel boots via TFTP before opening the PR.
4. Create `igc_single_queue_polling` from `igc_phy_bringup`.
5. Reconstruct the minimal polling datapath without shell/debug pieces.
6. After creating each later branch, repeat the same serial reboot validation before moving to the next branch.
7. Create each later branch from the previous roadmap branch in this order:
- `igc_observability`
- `igc_irq_rx_buffering`
- `igc_multi_queue`
- `igc_tx_csum_offload`
8. Open pull requests in the same order and keep them stacked until earlier ones merge.

## Commit mapping from `igc_fix`

- `2e5f21a9`: PR1 directly
- `b582d4ff`: PR2 core
- `89650d8b`: split between PR2 and PR3
- `a68d3bf8`: fold required DMA and bus-mastering pieces into PR2
- `f8e151a4`: PR4 directly
- `14c6239a`: PR5 directly
- `cabcbe56`: PR6 directly
