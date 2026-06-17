---
name: awkernel-async-scheduler-testing
description: Use when testing or debugging Awkernel async/await task scheduler behavior, including task kill, preemption, sleep/wake, timer interactions, QEMU reproduction, and SPIN model checking under specification/awkernel_async_lib/src/task/preemptive_spin.
---

# Awkernel Async Scheduler Testing

Use this skill when changing or reviewing `awkernel_async_lib` task scheduling behavior: `kill()`, preemption, sleep/wake, timer wakeups, task registry removal, or scheduler queues.

## Core workflow

1. Identify whether the issue is in runtime code, model code, or a test app.
2. Prefer `make` for kernel builds; do not replace kernel validation with direct `cargo` commands.
3. Reproduce on the smallest layer first, then escalate:
   - Rust/library check for compile-level regressions.
   - SPIN for scheduler state-machine properties.
   - RELEASE QEMU for real kernel behavior and shell responsiveness.
4. Treat shell stuck as a scheduler/timer symptom, not necessarily a shell bug.

## Build and QEMU commands

Use RELEASE builds for QEMU experiments:

```sh
make x86_64 RELEASE=1
make qemu-x86_64_nographic RELEASE=1
```

For kill-specific QEMU testing:

```sh
make x86_64 RELEASE=1 OPT='--release --features test_task_kill'
make qemu-x86_64_nographic RELEASE=1
```

After feature tests complete, verify the shell still responds with a small expression such as `(+ 7 8)`. Intentional panic logs from panic-specific tests are not automatically failures; check the PASS/FAIL lines after the panic.

## SPIN model checking

The preemptive scheduler model lives in:

```text
specification/awkernel_async_lib/src/task/preemptive_spin
```

Use the normal LTL tests for non-kill scheduler behavior:

```sh
make -C specification/awkernel_async_lib/src/task/preemptive_spin clean run
```

Use the kill-specific reduced model for kill behavior:

```sh
make -C specification/awkernel_async_lib/src/task/preemptive_spin clean kill-test
```

`kill-test` enables `KILL_TEST`, uses a smaller task set, and should keep killer/kill-only state out of normal `make run`. Do not run `clean run` and `clean kill-test` concurrently in the same directory; both targets delete and regenerate `pan.*` files.

## Scheduler failure patterns to check

- Stale task IDs: a running snapshot may reference a task removed from the registry by `kill()`.
- Terminal tasks: `Terminated` and `Panicked` tasks must not be requeued or selected for preemption.
- Deferred kill: `Preempted` tasks should set `kill_pending` and terminate at a safe await/resume point.
- Lock nesting: watch for self-deadlock around sleep/timer wake paths and global scheduler locks.
- Pending preemption: queues may contain tasks that become terminal before the interrupt handler consumes them.

## Generated files and commits

Do not commit SPIN or QEMU generated artifacts unless explicitly requested:

```text
pan
pan.*
*.trail
*_spin_nvr.tmp
kill-test-*.log
qemu-*.log
```

When committing scheduler work, include only source/model/test files relevant to the change. Leave unrelated dirty files untouched.
