# Verification Result

## Tools

- [loom](https://github.com/tokio-rs/loom)
- [Kani](https://github.com/model-checking/kani)
- [TLA+](https://github.com/tlaplus/tlaplus)

## Summary

| Target | Verification Code | Tool |
|--------|--------|-----|
| [MCS Lock](https://github.com/tier4/awkernel_sync/blob/main/src/mcs.rs) | [model_check_mcslock.rs](https://github.com/tier4/awkernel_sync/blob/main/tests/model_check_mcslock.rs) | loom |
| [RW Lock](https://github.com/tier4/awkernel_sync/blob/main/src/rwlock.rs) | [model_check_rwlock.rs](https://github.com/tier4/awkernel_sync/blob/main/tests/model_check_rwlock.rs) | loom |
| [Cooperative Async/await Scheduler](./awkernel_async_lib/src/task.rs) | [cooperative](./specification/awkernel_async_lib/src/task/cooperative/) | TLA+ |
| [Exception Handler of AArch64](./kernel/asm/aarch64/exception.S) | [exception.S](./specification/kernel/asm/aarch64/exception.S/) | TLA+ |
| [Context Switch of AArch64](./awkernel_lib/src/context/aarch64.rs) | [context/aarch64](./specification/awkernel_lib/src/context/aarch64/) | TLA+ |
| [Context Switch of x86_64](./awkernel_lib/src/context/x86_64.rs) | [context/x86](./specification/awkernel_lib/src/context/x86/) | TLA+ |
| [Delta List](./awkernel_async_lib_verified/src/delta_list.rs) | unit test | Kani |
| [Ring Queue](./awkernel_async_lib_verified/src/ringq.rs) | unit test | Kani |
