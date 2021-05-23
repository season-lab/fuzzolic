FROM ubuntu:18.04

RUN sed -i -- 's/# deb-src/deb-src/g' /etc/apt/sources.list && cat /etc/apt/sources.list

# dependencies
RUN apt update -y && \
	apt-get build-dep -y qemu-user && \ 
	apt install -y \
	llvm-8 clang-8 nano \
	qemu-user git libglib2.0-dev libfdt-dev \
	libpixman-1-dev zlib1g-dev libcapstone-dev \
	strace cmake python3 libprotobuf10 \
	libibverbs-dev libjpeg62-dev \
	libpng16-16 libjbig-dev \
	build-essential libtool-bin python3-dev \
	automake flex bison libglib2.0-dev \
	libpixman-1-dev clang \
	python3-setuptools llvm wget \
	llvm-dev g++ g++-multilib python \
	python-pip lsb-release gcc-4.8 g++-4.8 \
	llvm-3.9 cmake libc6 libstdc++6 \
	linux-libc-dev gcc-multilib \
	apt-transport-https libtool \
        libtool-bin wget \
        automake autoconf \
        bison git gdb dumb-init valgrind \
	time xxd python3-pip ninja-build && \
	apt clean && \
	rm -rf /var/lib/apt/lists/*

RUN groupadd --gid 1000 ubuntu \
    && useradd --uid 1000 --gid ubuntu --shell /bin/bash --create-home ubuntu

USER ubuntu

RUN python3 -m pip install --user virtualenv
RUN python3 -m pip install --user pytest
