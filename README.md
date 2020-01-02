# fuzzolic

A concolic executor into a fuzzer skeleton.

## QEMU

### Build
```
cd tracer
./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user
make -j4
```
### Run
Vanilla QEMU:
```
./tracer/x86_64-linux-user/qemu-x86_64 <path_to_binary> <binary_args>
```
QEMU with symbolic mode:
```
./tracer/x86_64-linux-user/qemu-x86_64 -symbolic <path_to_binary> <binary_args>
```
To configure the symbolic engine (needed to run correctly), a json file has to be created for the binary. 
See examples: `tests/simple-if.json`


