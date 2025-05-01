FROM debian:bookworm-slim AS intermediate
RUN apt-get -qq update; \
    apt-get install -qqy --no-install-recommends \
        gnupg2 wget ca-certificates apt-transport-https \
        autoconf automake cmake dpkg-dev file make patch libc6-dev

RUN echo "deb https://apt.llvm.org/bookworm llvm-toolchain-bookworm-18 main" \
        > /etc/apt/sources.list.d/llvm.list && \
    wget -qO /etc/apt/trusted.gpg.d/llvm.asc \
        https://apt.llvm.org/llvm-snapshot.gpg.key && \
    apt-get -qq update

RUN apt-get install -y curl

RUN curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- --default-toolchain 1.85.1 -y
ENV PATH="/root/.cargo/bin:$PATH"
#RUN /root/.cargo/bin/rustup install 1.85.1

RUN apt-get install -y lld-18 clang-18
RUN apt-get install -y gcc
RUN apt-get install -y llvm-18-dev

ENV LLVM_SYS_181_PREFIX=/usr/lib/llvm-18


RUN mkdir /src
WORKDIR /src
COPY .. .
RUN cargo test

#RUN apt-get install -qqy -t llvm-18-dev
#RUN apt-get install -qqy -t llvm-toolchain-buster-18 clang-18 clang-tidy-18 clang-format-18 lld-18 libc++-18-dev libc++abi-18-dev

#RUN apt update && \
#    apt upgrade -y && \
#    apt install clang cmake ninja-build git rustup -y
##RUN apt install pkg-config libssl-dev wget -y
#
#RUN mkdir /llvm
#WORKDIR /llvm
#RUN git clone https://github.com/llvm/llvm-project.git --depth 1 --branch llvmorg-18.1.8 src
#RUN mkdir /llvm/src/build
#WORKDIR /llvm/src/build
#RUN cmake ../llvm \
#    -DCMAKE_INSTALL_PREFIX=/llvm/llvm-18.1.8 \
#    -DCMAKE_BUILD_TYPE=Release \
#    -DLLVM_ENABLE_ASSERTIONS=ON \
#    -DLLVM_INCLUDE_TESTS=OFF \
#    -DLLVM_INCLUDE_EXAMPLES=OFF \
#    -DLLVM_INCLUDE_BENCHMARKS=OFF \
#    -DLLVM_ENABLE_PROJECTS="" \
#    -G Ninja
#RUN ninja
#RUN ninja install
#
##RUN rustup install 1.85.1
#
##RUN cargo install llvmenv
##ENV PATH="/root/.cargo/bin:$PATH"
##RUN llvmenv init
###RUN llvmenv entries
##RUN llvmenv build-entry 18.1
#
##RUN wget https://github.com/llvm/llvm-project/releases/download/llvmorg-18.1.8/llvm-18.1.8.src.tar.xz
##RUN apt install xz-utils -y
##RUN tar xJf llvm-18.1.8.src.tar.xz
##WORKDIR /llvm-18.1.8.src
##RUN mkdir build
##WORKDIR /llvm-18.1.8.src/build
##
