COUNT=3850

all: build-tracer build-solver kill-solver
	cat tests/simple_if_input_ko.dat | ./fuzzolic/fuzzolic.py tests/simple-if

simpleif: clean
	./solver/solver >/dev/null &
	cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -symbolic -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log
	grep 'IN: foo' -A $(COUNT) asm_in_out.log | head -n $(COUNT)
	wait

native:
	cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log
	grep 'IN: foo' -A 200 asm_in_out.log | head -n 200

configure:
	cd tracer && ./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user

kill-solver:
	killall -SIGINT solver || echo "No solver still alive to kill"

build-solver:
	cd solver && make build

build-tracer:
	cd tracer && make

core:
	sudo bash -c 'echo "core.%p.%s.%c.%d.%P" > /proc/sys/kernel/core_pattern'
	ulimit -c unlimited

clean:
	rm qemu_basic_2019* || echo

clean-shared:
	ipcrm -a
	ipcrm -m XXX
