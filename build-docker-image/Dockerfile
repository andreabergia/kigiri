FROM ubuntu:25.04 AS llvm-build
RUN apt update && \
    apt upgrade -y && \
    apt install clang cmake ninja-build git rustup -y
#RUN apt install pkg-config libssl-dev wget -y

RUN mkdir /llvm
WORKDIR /llvm
RUN git clone https://github.com/llvm/llvm-project.git --depth 1 --branch llvmorg-18.1.8 src
RUN mkdir /llvm/src/build
WORKDIR /llvm/src/build
RUN cmake ../llvm \
    -DCMAKE_INSTALL_PREFIX=/llvm/llvm-18.1.8 \
    -DCMAKE_BUILD_TYPE=Release \
    -DLLVM_ENABLE_ASSERTIONS=ON \
    -DLLVM_INCLUDE_TESTS=OFF \
    -DLLVM_INCLUDE_EXAMPLES=OFF \
    -DLLVM_INCLUDE_BENCHMARKS=OFF \
    -DLLVM_ENABLE_PROJECTS="" \
    -G Ninja
RUN ninja
RUN ninja install

#RUN rustup install 1.85.1

#RUN cargo install llvmenv
#ENV PATH="/root/.cargo/bin:$PATH"
#RUN llvmenv init
##RUN llvmenv entries
#RUN llvmenv build-entry 18.1

#RUN wget https://github.com/llvm/llvm-project/releases/download/llvmorg-18.1.8/llvm-18.1.8.src.tar.xz
#RUN apt install xz-utils -y
#RUN tar xJf llvm-18.1.8.src.tar.xz
#WORKDIR /llvm-18.1.8.src
#RUN mkdir build
#WORKDIR /llvm-18.1.8.src/build
#
