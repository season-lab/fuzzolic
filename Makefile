COUNT=3850

all: build-tracer build-solver kill-solver clean-work-dir
	./fuzzolic/fuzzolic.py tests/simple_if_input_ko.dat tests/simple-if
	./utils/print_test_cases.py workdir/tests

simpleif: clean-core kill-solver
	bash -c "env $(cat tests/simple-if.fuzzolic | xargs ) ./solver/solver >/dev/null &"
	bash -c "env $(cat tests/simple-if.fuzzolic | xargs ) cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -symbolic -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log"
	grep 'IN: foo' -A $(COUNT) asm_in_out.log | head -n $(COUNT)

native:
	cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log
	grep 'IN: foo' -A 200 asm_in_out.log | head -n 200

all-concrete: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py --debug out tests/all_concrete_ko.dat tests/all-concrete
	./utils/print_test_cases.py workdir/tests

all-concrete-full: build-tracer build-solver kill-solver clean-work-dir
	time -p ./fuzzolic/fuzzolic.py tests/all_concrete_ko.dat tests/all-concrete
	./utils/print_test_cases.py workdir/tests

strcmp-debug: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py --debug out tests/strcmp_d.dat tests/strcmp
	./utils/print_test_cases.py workdir/tests

strcmp: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py tests/strcmp_ko.dat tests/strcmp
	./utils/print_test_cases.py workdir/tests

mystrcmp: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py tests/strcmp_ko.dat tests/mystrcmp
	./utils/print_test_cases.py workdir/tests

configure:
	cd tracer && ./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user

clean-work-dir:
	rm -rf workdir

kill-solver:
	killall -SIGINT solver || echo "No solver still alive to kill"

build: build-solver build-tracer
	echo "Built."

build-solver:
	cd solver && make build

build-tracer:
	cd tracer && make

core:
	sudo bash -c 'echo "core.%p.%s.%c.%d.%P" > /proc/sys/kernel/core_pattern'
	ulimit -c unlimited

clean-core:
	rm qemu_basic_2019* || echo

clean-shared:
	ipcrm -a
	ipcrm -m XXX

print-tests:
	python utils/print_test_cases.py workdir/tests
