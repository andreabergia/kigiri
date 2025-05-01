FROM ubuntu:24.04
RUN apt update && \
    apt install -y \
      lsb-release \
      wget \
      software-properties-common \
      gnupg \
      rustup \
      build-essential \
      zlib1g-dev \
      libzstd-dev

RUN wget https://apt.llvm.org/llvm.sh && \
    chmod +x llvm.sh && \
    ./llvm.sh 18
RUN apt install -y \
      llvm-18-dev \
      libpolly-18-dev

RUN rustup install 1.85.1  --profile minimal --no-self-update
RUN rustup component add clippy
RUN cargo install cargo-nextest

#ENV LLVM_SYS_181_PREFIX=/usr/lib/llvm-18


RUN mkdir /src
WORKDIR /src
COPY .. .
#RUN cargo test
#RUN cargo clippy
#RUN cargo run
