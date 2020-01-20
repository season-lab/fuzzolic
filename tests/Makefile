all:
	gcc-4.8 driver.c adcq.s adcl.s adcw.s adcb.s addq.s addl.s addw.s addb.s simple_if.c mystrcmp.c all_concrete.c -o driver
	echo "SYMBOLIC_INJECT_INPUT_MODE=READ_FD_0" > driver.fuzzolic
	echo "SYMBOLIC_EXEC_START_ADDR=0x"`objdump -d driver | awk -v RS= '/^[[:xdigit:]]+ <foo>/' | head -n 2 | tail -n 1 | cut -f1 -d':' | tr -d '[:space:]'` >> driver.fuzzolic
	echo "SYMBOLIC_EXEC_STOP_ADDR=0x"`objdump -d driver | awk -v RS= '/^[[:xdigit:]]+ <foo>/' | tail -n 1 | cut -f1 -d':' | tr -d '[:space:]'` >> driver.fuzzolic

foostart:
	objdump -d driver | grep '<foo>:' | cut -f1 -d'<'

fooend:
	objdump -d driver | awk -v RS= '/^[[:xdigit:]]+ <foo>/' | tail -n 1 | cut -f1 -d':'| tr -d '[:space:]'


