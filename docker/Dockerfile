# FROM nvidia/cuda:11.7.0-runtime-ubuntu20.04
FROM ubuntu:22.04

ENV TZ=Asia/Tokyo
RUN ln -snf /usr/share/zoneinfo/$TZ /etc/localtime && echo $TZ > /etc/timezone

RUN apt-get -y update && \
    apt-get -y upgrade && \
    apt-get -y install build-essential zsh git curl libncurses5-dev \
    gnupg clang qemu-system-arm qemu-system-x86 vim telnet

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
RUN . /root/.cargo/env && \
    rustup toolchain install nightly && \
    rustup default nightly && \
    rustup component add rust-src llvm-tools-preview && \
    rustup target add x86_64-unknown-none aarch64-unknown-none-softfloat && \
    cargo install cargo-binutils

COPY zshenv /root/.zshenv
COPY zshrc /root/.zshrc

ENTRYPOINT ["zsh"]
