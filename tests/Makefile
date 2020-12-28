all: switch.o div3.o
	gcc-4.8 driver.c atoi.c adcq.s adcl.s adcw.s adcb.s addq.s addl.s \
		addw.s addb.s simple_if.c mystrcmp.c all_concrete.c switch.o \
		nested_if.c symbolic_index.c symbolic_read.c div3.o \
		model_strcmp.c model_strncmp.c model_strlen.c model_memcmp.c \
		model_memchr.c \
		-o driver
	echo "SYMBOLIC_INJECT_INPUT_MODE=READ_FD_0" > driver.fuzzolic
	echo "SYMBOLIC_EXEC_START_ADDR=0x"`objdump -d driver | awk -v RS= '/^[[:xdigit:]]+ <foo>/' | head -n 2 | tail -n 1 | cut -f1 -d':' | tr -d '[:space:]'` >> driver.fuzzolic
	echo "SYMBOLIC_EXEC_STOP_ADDR=0x"`objdump -d driver | awk -v RS= '/^[[:xdigit:]]+ <foo>/' | tail -n 1 | cut -f1 -d':' | tr -d '[:space:]'` >> driver.fuzzolic

div3.o: div3.c
	gcc-4.8 -c div3.c -O0

switch.o: switch.c
	gcc-4.8 -c switch.c -O0

foostart:
	objdump -d driver | grep '<foo>:' | cut -f1 -d'<'

fooend:
	objdump -d driver | awk -v RS= '/^[[:xdigit:]]+ <foo>/' | tail -n 1 | cut -f1 -d':'| tr -d '[:space:]'


run:
	@echo "Running tests using SMT solver"
	@python3 -m pytest run.py
	@echo "\nRunning tests using Fuzzy-SAT solver"
	@python3 -m pytest --fuzzy run.py

run-verbose:
	python3 -m pytest -v -s run.py
