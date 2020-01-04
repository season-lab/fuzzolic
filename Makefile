COUNT=3850

all: build-tracer build-solver kill-solver clean-work-dir
	./fuzzolic/fuzzolic.py tests/simple_if_input_ko.dat tests/simple-if
	./utils/print_test_cases.py workdir

simpleif: clean-core kill-solver
	bash -c "export `cat tests/simple-if.fuzzolic` && ./solver/solver >/dev/null & cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -symbolic -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log; wait"
	grep 'IN: foo' -A $(COUNT) asm_in_out.log | head -n $(COUNT)

native:
	cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log
	grep 'IN: foo' -A 200 asm_in_out.log | head -n 200

all-concrete: clean-core kill-solver
	bash -c "export `cat tests/all-concrete.fuzzolic` && ./solver/solver >/dev/null & cat tests/all_concrete_d.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -symbolic -d in_asm,op_opt,out_asm ./tests/all-concrete 2>asm_in_out.log; wait"
	grep 'IN: foo' -A $(COUNT) asm_in_out.log | head -n $(COUNT)

all-concrete-full: build-tracer build-solver kill-solver clean-work-dir
	time -p ./fuzzolic/fuzzolic.py tests/all_concrete_ko.dat tests/all-concrete
	./utils/print_test_cases.py workdir

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
