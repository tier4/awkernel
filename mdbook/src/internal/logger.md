# Logger

Awkernel uses [log](https://crates.io/crates/log) crate for logging.
So, you can use the log macros like defined in this crate as follows.
The logger uses the console module internally.

```rust
log::error!("This is an error message.");
log::warn!("This is a warning message.");
log::info!("Hello, world!");
log::debug!("This is a debug message.");
log::trace!("This is a trace message.");
```

`log::debug!` is useful when implementing and debugging the kernel
because it displays a message with the file name and line number where the macro is called.

You can use `log::set_max_level` function to set the maximum log level as follows.

```rust
log::set_max_level(log::LevelFilter::Trace);
```

# Buffered Logger

After booting Awkernel, the logger implementation defined in [awkernel_lib/src/logger.rs](https://github.com/tier4/awkernel/blob/main/awkernel_lib/src/logger.rs) is switched to a buffered logger defined in [applications/awkernel_services/src/buffered_logger.rs](https://github.com/tier4/awkernel/blob/main/applications/awkernel_services/src/buffered_logger.rs).
The buffered logger buffers log messages and writes them to the UART in a batch.
Note that the buffered logger will discard messages if the buffer is full to avoid memory exhaustion.
The buffered logger is executed as an async/await task and spawned in [applications/awkernel_services/src/main.rs](https://github.com/tier4/awkernel/blob/main/applications/awkernel_services/src/lib.rs).
