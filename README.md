# fuzzolic

A concolic executor into a fuzzer skeleton.

## QEMU

### Build
```
cd qemu
./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user
make -j4
```
### Run
Vanilla QEMU:
```
./qemu/x86_64-linux-user/qemu-x86_64 <path_to_binary> <binary_args>
```
QEMU with symbolic mode:
```
./qemu/x86_64-linux-user/qemu-x86_64 -symbolic <path_to_binary> <bianry_args>
```
To inject symbolic inputs during the binary execution, see `qemu/tcg/symbolic/config.h`.

