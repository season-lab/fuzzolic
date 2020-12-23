# Usage

## Fuzzy-SAT (cli)

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

It takes as mandatory command line arguments an smt2 query file with `--query` and a seed file with `--seed`. Optionally, the user can specify an output folder (`--out`) where the program dump the sat queries (`--dsat`) and the assignments for sat queries (`--dproofs`). `fuzzy-solver` will try to solve every _assert_ contained in the _smt2_ file.

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
 * `--afl AFL_WORKDIR`: this enables the AFL model, see next section;
 * `--timeout TIMEOUT`: maximum cumulative solving time (ms) within one path exploration;
 * `--optimistic-solving`: this enables optimistic solving;
 * `--single-path`: fuzzolic will perform a single-path exploration (first input from the seed directory)
 * `--keep-run-dirs`: intermediate run directories (`workdir/fuzzolic-XXXXX`), containing tracer/solver logs and generated testcases (before discarding uninteresting ones), will not be deleted when this option is set;
 * `--address-reasoning`: fuzzolic will try to generate testcases that cover different memory addresses when detecting a symbolic pointer during the exploration.
 
 The full list of fuzzolic options can be seen using `./fuzzolic/fuzzolic.py --help`.

After (and during) an exploration, the workdir will typically contain the following files:
* `{afl-bitmap, afl-crash-bitmap, branch_bitmap, context_bitmap}`: bitmaps used by fuzzolic to evaluate whether a branch query is interesting;
* `fuzzolic-XXXXX/` (kept only when `--keep-run-dirs` is used): e.g., `{fuzzolic-00000, fuzzolic-00001, ...}`
	* `solver.log`: log of the solver backend
	* `tracer.log`: log of the tracer
	* `test_case_ZZZ_YYY.dat`: e.g., `test_case_0_0.dat`, a test case generated by fuzzolic for path id=`XXXXXX` when processing query with id=`ZZZ`
* `queue/`: 
	* when in standalone mode: test cases (from the seed directory or from previous `fuzzolic-XXXXX/` directories) that still need to be processed by fuzzolic during the current exploration
	* when in AFL mode: interesting test cases generated by fuzzolic
* `tests/`:
	* when in standalone mode: interesting test cases generated by fuzzolic
	* when in AFL mode: not used

Hence, when looking for interesting test cases generated by fuzzolic, check the directory `tests` when using fuzzolic in standalone mode. On the other hand, check the directory `queue` when using fuzzolic in AFL mode.

### Example



## Hybrid fuzzing (AFL mode)
