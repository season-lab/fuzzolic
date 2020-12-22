# Usage

## Fuzzy-SAT (cli)

The program `fuzzy-solver` can be used to solve SMT queries using the Fuzzy-SAT algorithm. It takes as input an SMT file, and a binary seed file:

```
$ fuzzy-solver query.smt2 seed.bin
```

The symbols in the smt2 file MUST be declared as 8-bit bitvectors, and they must be named `k!<i>`, where `<i>` is the index of the i-th byte in the seed that represents the initial assignment for that symbol.

*Example*:
__query.smt2__
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

__seed.bin__
```
0000
```

`fuzzy-solver` will try to solve every __assert__ contained in the __smt2__ file, and will print to stdout the number of queries proved SAT, and the elapsed time.

If the user provides an output directory (`--outdir=DIR`), `fuzzy-solver` will dump assignments for SAT queries (one for each assert) to the directory as binary files (using the same convetion of the seed). **TO BE IMPLEMENTED**

## Concolic execution (standalone)

## Hybrid fuzzing (AFL mode)
