# Usage

## Fuzzy-SAT

### Command-line interface

The program `fuzzy-solver` can be used to solve SMT queries using the Fuzzy-SAT algorithm:

```
$ fuzzy-solver --help

Usage: ./build/bin/fuzzy-solver [OPTIONS]
  -h, --help                print this help and exit
  -q, --query               SMT2 query filename (required)
  -s, --seed                binary seed file (required)
  -o, --out                 output directory

  --dsat                    dump sat queries
  --dproofs                 dump sat proofs
  --notui                   no text UI
```

It takes as mandatory command line arguments an smt2 query file with `--query` and a seed file with `--seed`. Optionally, the user can specify an output folder (`--out`) where it dumps the sat queries (`--dsat`) and the assignments for sat queries (`--dproofs`).

`fuzzy-solver` will try to solve every _assert_ contained in the _smt2_ file.
Note that the symbols in the smt2 file MUST be declared as 8-bit bitvectors, and they must be named `k!<i>`, where `<i>` is the index of the i-th byte in the seed that represents the initial assignment for that symbol. This is an example of smt2 query and seed file:

_query.smt2_
``` smt2
(declare-const k!0 (_ BitVec 8))
(declare-const k!1 (_ BitVec 8))
(declare-const k!2 (_ BitVec 8))
(declare-const k!3 (_ BitVec 8))

(assert 
    (= 
        #xdeadbeef 
        (bvadd 
            (concat k!0 k!1 k!2 k!3)
            #xabadcafe))
)
```

_seed.bin_
```
0000
```

#### Text UI

By default, `fuzzy-solver` uses a text UI where it prints useful statistics about the solving process:
```
   query 992/992
 o-------------------------------------------------------------o
 | num eval:   400528        sat:        147 (1) [727 opt]     |
 |                                                             |
 | its:        91            its ext:    14                    |
 | sm:         8             bf:         11                    |
 | rbf:        4             rbf opt:    6                     |
 | gd:         0             havoc:      0                     |
 | bit flips:  8, 0, 0       byte flips: 0, 0, 0, 0            |
 | arithms:    0             ints:       0                     |
 | multigoal:  5             fallbacks:  164 (1120)si (115)nt  |
 |                                                             |
 | # confl:          1203    # univ def:          0            |
 | confl cache size: 198     ast info cache size: 5378         |
 | num timeouts:     0       ast info cache hits: 6387         |
 |                                                             |
 | avg eval time: 1.293 usec                                   |
 o-------------------------------------------------------------o
```

[...]

### C/C++ Bindings

## Concolic execution (standalone mode)

To run fuzzolic in standalone mode, you need to execute the script `./fuzzolic/fuzzolic.py`. For instance:
```
$ ./fuzzolic/fuzzolic.py -o ./workdir -i ./seeds -- ./program [args] @@
```
will run concolic execution on `./program`, passing (optional) arguments `args`, using initial inputs available in the directory `seeds`, generating the results in the directory `./workdir`. Similarly to AFL, since `@@` is specified for the program, then fuzzolic will assume that the program is getting the input from a file stored on the filesystem (fuzzolic will replace `@@` with the correct path at runtime). When `@@` is not used, fuzzolic will assume that the input is obtained by reading from the standard input. The exploration will follow multiple paths, halting when no new interesting inputs can be generated anymore by fuzzolic. 

By default, fuzzolic will use the SMT solver Z3. To select Fuzzy-SAT as the solver backend, add the option `-f` (or `--fuzzy`):
```
$ ./fuzzolic/fuzzolic.py -f -o ./workdir -i ./seeds -- ./program [args] @@
```
Several other options can be set to enable additional features:
 * `--afl AFL_WORKDIR`: this enables the AFL mode, see next section;
 * `--timeout TIMEOUT`: maximum cumulative solving time (ms) within one path exploration;
 * `--optimistic-solving`: this enables optimistic solving;
 * `--single-path`: fuzzolic will perform a single-path exploration (first input from the seed directory)
 * `--keep-run-dirs`: intermediate run directories (`workdir/fuzzolic-XXXXX`), containing tracer/solver logs and generated testcases (before discarding uninteresting ones), will not be deleted when this option is set;
 * `--address-reasoning`: fuzzolic will try to generate testcases that cover different memory addresses when detecting a symbolic pointer during the exploration.
 * `--symbolic-models`: fuzzolic will use models to reason over known libc functions (e.g., `memcpy`).
 
 The full list of fuzzolic options can be seen using `./fuzzolic/fuzzolic.py --help`.

After (and during) an exploration, the workdir will typically contain the following files:
* `{afl-bitmap, afl-crash-bitmap, branch_bitmap, context_bitmap}`: bitmaps used by fuzzolic to evaluate whether a branch query is interesting;
* `fuzzolic-XXXXX/` (kept only when `--keep-run-dirs` is used): e.g., `{fuzzolic-00000, fuzzolic-00001, ...}`
	* `solver.log`: log of the solver backend
	* `tracer.log`: log of the QEMU tracer
	* `test_case_ZZZ_YYY.dat`: e.g., `test_case_0_0.dat`, a test case generated by fuzzolic for path id=`XXXXXX` when processing query with id=`ZZZ`
* `queue/`: 
	* when in standalone mode: test cases (from the seed directory or from previous `fuzzolic-XXXXX/` directories) that still need to be processed by fuzzolic during the current exploration
	* when in AFL mode: interesting test cases generated by fuzzolic
* `tests/`:
	* when in standalone mode: interesting test cases generated by fuzzolic
	* when in AFL mode: not used

Hence, when looking for interesting test cases generated by fuzzolic, check the directory `tests` when using fuzzolic in standalone mode. On the other hand, when using fuzzolic in AFL mode check the directory `queue`.

### Example

Let us consider the program [`tests/example/example.c`](https://github.com/season-lab/fuzzolic/blob/master/tests/example/example.c#L21):
```
#include <stdio.h>
#include <stdlib.h>

int magic_check(int p){
    if (p == 0xDEADBEEF)
        return 1;
    else
        return 0;
}

int get_input(char* fname) {
    FILE* fp = fopen(fname, "r");
    if (fp == NULL) exit(EXIT_FAILURE);
    int data;
    int r = fread(&data, 1, sizeof(data), fp);
    if (r != sizeof(data)) exit(EXIT_FAILURE);
    fclose(fp);
    return data;
}

int main(int argc, char* argv[]) {

    if (argc != 2) exit(EXIT_FAILURE);
    int input = get_input(argv[1]); // read four bytes from the input file
    if (magic_check(input)) {
        printf("Correct value [%x] :)\n", input);
    } else {
        printf("Wrong value [%x] :(\n", input);
    }

    return 0;
}
```
Our goal is to automatically find the magic value `0xDEADBEEF` that is expected by the function `magic_check`. Since we do not know the magic value beforehand, we consider as an initial seed a file ([`tests/example/inputs/seed.dat`](https://github.com/season-lab/fuzzolic/blob/master/tests/example/inputs/seed.dat)) containing just the `AAAA\n` characters. Moreover, since fuzzolic is a binary concolic executor, we need to compile the example into a working binary:
```
$ gcc -o  tests/example/example tests/example/example.c
```
If we run the program over the initial seed:
```
$ ./tests/example/example tests/example/inputs/seed.dat 
```
we should get the following output:
```
Wrong value [41414141] :(
```

Now, if we instead start the concolic exploration with fuzzolic:
```
$ ./fuzzolic/fuzzolic.py -o ./workdir/ -i tests/example/inputs/ -- ./tests/example/example @@
```
The output should be similar to:
```
Configuration file for /home/ubuntu/fuzzolic/tests/example/example is missing. Using default configuration.

Running directory: /home/ubuntu/fuzzolic/workdir/fuzzolic-00000
Using SMT solver
[-] Discarding test_case_11_0.dat
[-] Discarding test_case_3_0.dat
[+] Keeping test_case_1_0.dat
[-] Discarding test_case_7_0.dat
[-] Discarding test_case_5_0.dat
Run took 0.3 secs

Running directory: /home/ubuntu/fuzzolic/workdir/fuzzolic-00001
Using SMT solver
[-] Discarding test_case_1_0.dat
Run took 0.2 secs
[FUZZOLIC] no more testcase. Finishing.
```
We can see that fuzzolic has generated 6 testcases (`test_case_{1, 3, 5, 7, 11}_0.dat`) during run with id=`00000`, where the first one (`test_case_1_0.dat`) is due to the internal check from the `magic_check` function, while the other ones are due to the `printf` function inside the `main` function (which performs some checks). Moreover, we can see that fuzzolic is keeping only the first test case (see `[+]` in the output) and is discarding the other ones (see `[-]` in the output): only the first test case bring more code coverage in the program. Test case `test_case_1_0.dat` is copied (renaming it as `test_case_000_000.dat`) into both the `queue` and `tests` directories. In the second run (id=`00001`), fuzzolic performs another exploration using the new input (picking it from the queue) and generates only a single test case (`test_case_1_0.dat`), which is however dubbed uninteresting and thus discarded.

If we check the content of the generated test case using `xxd`:
```
$ xxd workdir/tests/test_case_000_000.dat
00000000: efbe adde 0a 
```
we can see that it contains five bytes, where the first four bytes are the little endian representation of `0xdeadbeef`.
To test that fuzzolic has indeed found the correct input, we can run again the example program on the generated test case:
```
$ ./tests/example/example workdir/tests/test_case_000_000.dat 
Correct value [deadbeef] :)
```
and see that the input is accepted by the program.

## Hybrid fuzzing (AFL mode)
