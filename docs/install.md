# Installation

## Docker container
A prebuilt container image is available on Docker Hub. You can pull and launch it with:
```
$ docker run -ti --rm ercoppa/fuzzolic-runner-v1:ubuntu2004
```

## Manual build
Fuzzolic and fuzzy-sat have been tested on Ubuntu 18.04/20.04 x86_64. A manual installation requires to build:
 * our custom fork of Z3
 * fuzzy-sat
 * fuzzolic tracer based on QEMU
 * fuzzolic solver frontend 
 * AFL++

Some of these dependencies are included as submodules, hence to build fuzzolic you first need to fetch them:
```
$ git submodule sync && git submodule update --init
$ cd solver/fuzzy-sat && git fetch && git submodule sync && git submodule update --init
```

Step-by-step instructions for compiling these components can be found inside the [`Dockerfile`](https://github.com/season-lab/fuzzolic/blob/master/docker/fuzzolic-runner/Dockerfile.Ubuntu2004).

## Running tests
To test your installation of fuzzolic and fuzzy-sat, you can run some tests from the root of project:
```
$ cd tests
$ make run
```
The expected output should be similar to:
```
Running tests using SMT solver
============================= test session starts ==============================
platform linux -- Python 3.6.9, pytest-6.2.1, py-1.10.0, pluggy-0.13.1
rootdir: /home/ubuntu/fuzzolic/tests
collected 14 items                                                             

run.py ..............                                                    [100%]

============================= 14 passed in 16.04s ==============================

Running tests using Fuzzy-SAT solver
============================= test session starts ==============================
platform linux -- Python 3.6.9, pytest-6.2.1, py-1.10.0, pluggy-0.13.1
rootdir: /home/ubuntu/fuzzolic/tests
collected 14 items                                                             

run.py ..............                                                    [100%]

============================= 14 passed in 15.98s ==============================
```
The number of executed tests and the running time may differ.
