# fuzzolic

A concolic executor into a fuzzer skeleton.

## QEMU
```
cd qemu
./configure --prefix=`pwd`/../inst --target-list=i386-linux-user,x86_64-linux-user
make -j4
```
