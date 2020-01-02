# fuzzolic

A concolic executor into a fuzzer skeleton.

## QEMU

### Build
```
cd tracer
./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user
make -j4
```

## Run
```
./fuzzolic/fuzzolic.py <binary> <seed>
```
To configure the symbolic exploration, a JSON file (`<binary>.json`) should define a few parameters for the current binary. See as an example `tests/simple-if.json`.
