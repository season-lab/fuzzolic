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
	time xxd && \
	apt clean && \
	rm -rf /var/lib/apt/lists/*

# user 1000
RUN groupadd --gid 1000 ubuntu \
    && useradd --uid 1000 --gid ubuntu --shell /bin/bash --create-home ubuntu

USER ubuntu

RUN pip install --user virtualenv

COPY --chown=1000:1000 . /home/ubuntu/fuzzolic

WORKDIR /home/ubuntu/fuzzolic

# Build QEMU tracer
RUN cd tracer && ./configure --prefix=`pwd`/../build --target-list=x86_64-linux-user && make -j `nproc` 

# Build custom Z3
RUN cd solver/fuzzy-sat/fuzzolic-z3 && mkdir build && cd build && cmake .. -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=`pwd`/dist && make -j `nproc` && make install

# Set environment vars for Z3
ENV C_INCLUDE_PATH=/home/ubuntu/fuzzolic/solver/fuzzy-sat/fuzzolic-z3/build/dist/include
ENV LIBRARY_PATH=/home/ubuntu/fuzzolic/solver/fuzzy-sat/fuzzolic-z3/build/dist/lib
ENV LD_LIBRARY_PATH=/home/ubuntu/fuzzolic/solver/fuzzy-sat/fuzzolic-z3/build/dist/lib
ENV BASH_ENV=/home/ubuntu/.bashrc
RUN echo "export C_INCLUDE_PATH=/home/ubuntu/fuzzolic/solver/fuzzy-sat/fuzzolic-z3/build/dist/include" >> $BASH_ENV
RUN echo "export LIBRARY_PATH=/home/ubuntu/fuzzolic/solver/fuzzy-sat/fuzzolic-z3/build/dist/lib" >> $BASH_ENV
RUN echo "export LD_LIBRARY_PATH=/home/ubuntu/fuzzolic/solver/fuzzy-sat/fuzzolic-z3/build/dist/lib" >> $BASH_ENV

# Build fuzzy-sat
RUN cd solver/fuzzy-sat && make -j `nproc`

# Build solver frontend
RUN cd solver && cmake . && make -j `nproc`

# Build AFL++
RUN cd utils && git clone https://github.com/AFLplusplus/AFLplusplus.git && \
	cd AFLplusplus && git checkout 9dbace240d570f8eb938db5a152e31756922b2f3 && \
	git apply ../afl-showmap.c.patch && \
	make -j `nproc` all && cd qemu_mode && ./build_qemu_support.sh
ENV AFL_PATH=/home/ubuntu/fuzzolic/utils/AFLplusplus
RUN echo "export AFL_PATH=/home/ubuntu/fuzzolic/utils/AFLplusplus" >> $BASH_ENV

CMD bash