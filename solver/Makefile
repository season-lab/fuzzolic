build:
	gcc -o solver main.c -O3 -lz3

fuzzy: 
	gcc -o solver testcase-list.c fuzzy-solver.c -O3 -lz3

run: build
	./solver
