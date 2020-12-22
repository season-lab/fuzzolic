# Usage

## Fuzzy-SAT (cli)

The program `fuzzy-solver` can be used to solve SMT queries using the Fuzzy-SAT algorithm. It takes as input an SMT file, and a binary seed file:

```
$ fuzzy-solver query.smt2 seed.bin
```

The symbols in the smt2 file MUST be declared as 8-bit bitvectors, and they must be named `k!<i>`, where `<i>` is the index of the i-th byte in the seed that represents the initial assignment for that symbol.

**Example**:

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

`fuzzy-solver` will try to solve every _assert_ contained in the _smt2_ file, and will print to stdout the number of queries proved SAT, and the elapsed time.

If the user provides an output directory (`--outdir=DIR`), `fuzzy-solver` will dump assignments for SAT queries (one for each assert) to the directory as binary files (using the same convetion of the seed). *TO BE IMPLEMENTED*

## Concolic execution (standalone mode)

To run fuzzolic in standalone mode, you need to execute the `./fuzzolic/fuzzolic.py` script. For instance:
```
$ ./fuzzolic/fuzzolic.py -o ./workdir -i ./seeds -- ./program [args] @@
```
will run concolic execution on `./program`, passing (optional) arguments `args`, using initial inputs available in the directory `seeds`, generating the results in the directory `./workdir`. Similarly to AFL, since `@@` is specified for the program, the fuzzolic is assuming that the program is getting the input from a file stored on the filesystem (fuzzolic will replace `@@` with the correct path at runtime). When `@@` is not used, fuzzolic will assume that the input is obtained by reading from the standard input. The exploration will follow multiple paths, halting when no new interesting inputs can be generated anymore by fuzzolic. 

In the previous experiment, fuzzolic will use the SMT solver Z3. To select Fuzzy-SAT as the solver backend, add the option `-f` (or `--fuzzy`):
```
$ ./fuzzolic/fuzzolic.py -f -o ./workdir -i ./seeds -- ./program [args] @@
```

## Hybrid fuzzing (AFL mode)
