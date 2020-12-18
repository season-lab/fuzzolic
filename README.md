# Fuzzolic

fuzzing + concolic = fuzzolic :\)

## Build

### QEMU

```text
cd tracer
./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user
make -j4
```

### Z3

Install Z3 normally.

## Run

```text
./fuzzolic/fuzzolic.py <seed> <binary> [<args> ...]
```

To run the symbolic exploration, a configuration file \(`<binary>.fuzzolic`\) must exist.  
See as an example `tests/simple-if.fuzzolic`.

Results are stored in `./workdir`.
