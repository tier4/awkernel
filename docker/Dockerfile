FROM ubuntu:24.04

RUN apt-get -y update && \
    apt-get -y upgrade && \
    apt-get -y install build-essential zsh git curl libncurses5-dev \
    gnupg clang qemu-system-arm qemu-system-x86 vim telnet python3-pyelftools

ENV CARGO_HOME /usr/local/cargo
ENV RUSTUP_HOME /usr/local/rustup

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y

RUN . /usr/local/cargo/env && \
    cargo install cargo-binutils && \
    cargo install mdbook && \
    cargo install mdbook-mermaid

RUN . /usr/local/cargo/env && \
    rustup toolchain install nightly-2025-04-29 && \
    rustup default nightly-2025-04-29 && \
    rustup component add rust-src llvm-tools-preview && \
    rustup target add x86_64-unknown-none aarch64-unknown-none riscv32imac-unknown-none-elf

RUN chmod -R a+rw /usr/local/cargo

#COPY zshenv /root/.zshenv
#COPY zshrc /root/.zshrc

CMD ["/bin/bash"]
