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

It takes as mandatory command-line arguments an smt2 query file with `--query` and a seed file with `--seed`. Optionally, the user can specify an output folder (`--out`) where it dumps the sat queries (`--dsat`) and the assignments for sat queries (`--dproofs`).

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

If you are using the `fuzzolic-runner` container, you can find the executable in `~/solver/fuzzy-solver-cli/build/bin/fuzzy-solver`.

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

### C/C++ Bindings
We designed FuzzySAT as a library to be integrated into a concolic executor. Before detailing the various APIs, let us clarify some details on the usage of the library:

- The APIs that take an AST as input expect as symbols only 8-bit bitvectors whose symbol name has been created using `Z3_mk_int_symbol`. This allows the library to easily map a symbol to its assignment.
- The context of Z3 can be created either with `Z3_mk_context` or `Z3_mk_context_rc`, allowing the lib to be used with both the C and the C++ APIs of Z3.
- At the moment, the library is NOT thread-safe.

#### z3fuzz_init
```
void z3fuzz_init(fuzzy_ctx_t* ctx, Z3_context z3_ctx, char*   seed_filename,
                 void* /* NULL */, void* /* NULL */, unsigned timeout)
```
It initializes the context of the solver:
- `ctx`: The context of the solver to be initialized.
- `z3_ctx`: The z3 context (already initialized).
- `seed_filename`: The filename of the seed.
- `timeout`: Timeout for trying to solve a query in ms. If zero, no timeout.

#### z3fuzz_free
```
void z3fuzz_free(fuzzy_ctx_t* ctx);
```
It releases all the memory allocated by `z3fuzz_init`.

#### z3fuzz_evaluate_expression
```
unsigned long z3fuzz_evaluate_expression(fuzzy_ctx_t* ctx, Z3_ast expr,
                                         unsigned char* values);
```
It evaluates the expression `expr` using as assignments the values in the array `values`.

#### z3fuzz_query_check_light
```
int z3fuzz_query_check_light(fuzzy_ctx_t* ctx, Z3_ast pi,
                             Z3_ast                branch_condition,
                             unsigned char const** proof,
                             unsigned long*        proof_size);
```
It tries to solve the query `branch_condition ^ pi` using the FuzzySAT algorithm.
- `ctx`: The context of the solver.
- `pi`: The path constraint.
- `branch_condition`: The branch condition.
- `proof`: Output buffer that contains the resulting assignment if the function returns `1`.
- `proof_size`: Output value that contains the resulting length of assignment if the function returns `1`.

The function succeeds if it returns `1`.

#### z3fuzz_get_optimistic_sol
```
int z3fuzz_get_optimistic_sol(fuzzy_ctx_t* ctx, unsigned char const** proof,
                              unsigned long* proof_size);
```
If the last call to `z3fuzz_query_check_light` failed, this function tries to find an assignment for the `branch_condition` of the last query, ignoring `pi`.
- `ctx`: The context of the solver.
- `proof`: Output buffer that contains the resulting assignment if the function returns `1`.
- `proof_size`: Output value that contains the resulting length of assignment if the function returns `1`.

The function succeeds if it returns `1`.

#### z3fuzz_maximize and z3fuzz_minimize
```
unsigned long z3fuzz_maximize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_maximize,
                              unsigned char const** out_values,
                              unsigned long*        out_len);
unsigned long z3fuzz_minimize(fuzzy_ctx_t* ctx, Z3_ast pi, Z3_ast to_minimize,
                              unsigned char const** out_values,
                              unsigned long*        out_len);
```
They try to minimize/maximize the expression given the constraints in `pi`. The functions assume that `pi` evaluates as True in the seed.
- `ctx`: The context of the solver.
- `to_maximize` / `to_minimize`: The expression to maximize/minimize. It must be a bitvector.
- `out_values`: Output buffer that contains the assignments that maximize/minimize the expression.
- `out_len`: Output variable that contains the size of the `out_values` buffer.

The function always succeeds (but it is not guaranteed that it finds a global minimum/maximum) and returns the value of the maximized/minimized expression.

#### z3fuzz_find_all_values and z3fuzz_find_all_values_gd
```
typedef enum fuzzy_findall_res_t {
    Z3FUZZ_GIVE_NEXT,
    Z3FUZZ_STOP
} fuzzy_findall_res_t;

void z3fuzz_find_all_values(
    fuzzy_ctx_t* ctx, Z3_ast expr, Z3_ast pi,
    fuzzy_findall_res_t (*callback)(unsigned char const* out_bytes,
                                    unsigned long        out_bytes_len,
                                    unsigned long        val));
void z3fuzz_find_all_values_gd(
    fuzzy_ctx_t* ctx, Z3_ast expr, Z3_ast pi, int to_min,
    fuzzy_findall_res_t (*callback)(unsigned char const* out_bytes,
                                    unsigned long        out_bytes_len,
                                    unsigned long        val));
```
They generate valid assignments for the expression `expr` given the path constraint `pi`.
The user must define a `callback` that is called every time the function generates a new assignment. The callback can return `Z3FUZZ_GIVE_NEXT` to ask for another value or `Z3FUZZ_STOP` to stop.

The only difference between `z3fuzz_find_all_values_gd` and `z3fuzz_find_all_values` is that the former uses gradient descent to generate the values, and has an additional parameter (`to_min`) that specify the direction (towards the maximum or the minimum).

#### z3fuzz_notify_constraint
```
void z3fuzz_notify_constraint(fuzzy_ctx_t* ctx, Z3_ast constraint);
```
It notifies the solver that a new constraint has been added to `pi`.

#### z3fuzz_dump_proof
```
void z3fuzz_dump_proof(fuzzy_ctx_t* ctx, const char* filename,
                       unsigned char const* proof, unsigned long proof_size);
```
It dumps a proof returned by `z3fuzz_query_check_light` or `z3fuzz_get_optimistic_sol` on the file specified in `filename`.

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
 * `-a, --afl AFL_WORKDIR`: this enables the AFL mode, see [next section](#hybrid-fuzzing-afl-mode);
 * `-t, --timeout TIMEOUT`: maximum cumulative solving time (ms) within one path exploration;
 * `-p, --optimistic-solving`: this enables optimistic solving;
 * `-k, --single-path`: fuzzolic will perform a single-path exploration (first input from the seed directory)
 * `--keep-run-dirs`: intermediate run directories (`workdir/fuzzolic-XXXXX`), containing tracer/solver logs and generated testcases (before discarding uninteresting ones), will not be deleted when this option is set;
 * `-r, --address-reasoning`: fuzzolic will try to generate testcases that cover different memory addresses when detecting a symbolic pointer during the exploration;
 * `-l, --symbolic-models`: fuzzolic will use models to reason over known libc functions (e.g., `memcpy`).
 
 The full list of fuzzolic options can be seen using `./fuzzolic/fuzzolic.py --help`.
 
The options used for the ICSE paper are:
* when using FUZZY-SAT: `--fuzzy`, `--address-reasoning`, `--optimistic-solving`, `--timeout 90000`
* when using Z3: `--address-reasoning`, `--optimistic-solving`, `--timeout 90000`

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
$ ./fuzzolic/fuzzolic.py --address-reasoning --optimistic-solving --timeout 90000 -o ./workdir/ -i tests/example/inputs/ -- ./tests/example/example @@
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

To run fuzzolic in parallel with AFL++, you can use the script `fuzzolic/run_afl_fuzzolic.py` which supports most features from fuzzolic. For instance, to fuzz a program `lodepng` which takes as argument the input file to process, then:
```
$ ./fuzzolic/run_afl_fuzzolic.py --address-reasoning --optimistic-solving --timeout 90000 --fuzzy -o workdir/ -i ../benchmarks/lodepng/seeds/ -- ../benchmarks/lodepng/lodepng @
```
The output should be similar to:
```
Running: /home/ubuntu/fuzzolic/utils/AFLplusplus/afl-fuzz -c 0 -M afl-master -o workdir/ -i ../benchmarks/lodepng/seeds/ -Q -- ../benchmarks/lodepng/lodepng @@
Waiting 30 seconds before starting slave.
Running: /home/ubuntu/fuzzolic/utils/AFLplusplus/afl-fuzz -S afl-slave -o workdir/ -i ../benchmarks/lodepng/seeds/ -Q ../benchmarks/lodepng/lodepng @@
Waiting 30 seconds before starting fuzzolic.
Running: /home/ubuntu/fuzzolic/fuzzolic/fuzzolic.py -f -p -r -a workdir//afl-slave/ -i workdir//afl-slave/queue/ -o workdir//fuzzolic -- ../benchmarks/lodepng/lodepng @@
Configuration file for /home/ubuntu/benchmarks/lodepng/lodepng_decode_cg_nocksm is missing. Using default configuration.

Running directory: /home/ubuntu/fuzzolic/workdir/fuzzolic/fuzzolic-00000
Using Fuzzy-SAT solver
Run took 0.2 secs

Running directory: /home/ubuntu/fuzzolic/workdir/fuzzolic/fuzzolic-00001
Using Fuzzy-SAT solver
[+] Keeping test_case_6_0.dat
[+] Keeping test_case_11_0.dat
[-] Discarding test_case_13_0.dat
[+] Keeping test_case_3_0.dat
[+] Keeping test_case_12_0.dat
[+] Keeping test_case_14_0.dat
[+] Keeping test_case_15_666.dat
[+] Keeping test_case_1_0.dat
[-] Discarding test_case_9_0.dat
[+] Keeping test_case_10_0.dat
[+] Keeping test_case_8_0.dat
[+] Keeping test_case_4_0.dat
[+] Keeping test_case_7_0.dat
[+] Keeping test_case_2_0.dat
[+] Keeping test_case_5_0.dat
Run took 0.2 secs

[...]
```
The generated inputs can be found in `<output_dir>/*/queue/`, i.e.:
* `<output_dir>/afl-master/queue/`
* `<output_dir>/afl-slave/queue/`
* `<output_dir>/fuzzolic/queue/`

while crashing inputs under `<output_dir>/*/crashes/`. Inputs generated by fuzzolic will have the expected format for parallel mode: `id:XXXXXX,src:id:YYYYYY`, where `XXXXXX` is an incremental id assigned by fuzzolic to its own inputs and `YYYYYYYY` is the id of the input that was picked by fuzzolic from the queue of the slave and used during the exploration that has generated the new input `XXXXXX`.

To run AFL++ with additional flags, you can use `-g, --afl-args "<args>"`. E.g.:
```
./fuzzolic/run_afl_fuzzolic.py -o workdir/ -i ../benchmarks/lodepng/seeds/ -g "-m 1G" -- ../benchmarks/lodepng/lodepng @@
```
will set the additional arguments `-m 1G` for AFL++:
```
Running: /home/ubuntu/fuzzolic/utils/AFLplusplus/afl-fuzz -c 0 -M afl-master -o workdir/ -i ../benchmarks/lodepng/seeds/ -m 1G -Q -- ../benchmarks/lodepng/lodepng @@
Waiting 30 seconds before starting slave.
Running: /home/ubuntu/fuzzolic/utils/AFLplusplus/afl-fuzz -S afl-slave -o workdir/ -i ../benchmarks/lodepng/seeds/ -m 1G -Q ../benchmarks/lodepng/lodepng @@
Waiting 30 seconds before starting fuzzolic.
[...]
```
