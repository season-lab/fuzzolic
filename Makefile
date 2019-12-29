COUNT=3850

all: clean
	./tracer/x86_64-linux-user/qemu-x86_64 -symbolic -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log
	grep 'IN: foo' -A $(COUNT) asm_in_out.log | head -n $(COUNT)

native:
	./tracer/x86_64-linux-user/qemu-x86_64 -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log
	grep 'IN: foo' -A 200 asm_in_out.log | head -n 200

configure:
	cd tracer && ./configure --prefix=`pwd`/../build --target-list=i386-linux-user,x86_64-linux-user

build:
	cd tracer && make

core:
	sudo bash -c 'echo "core.%p.%s.%c.%d.%P" > /proc/sys/kernel/core_pattern'
	ulimit -c unlimited

clean:
	rm qemu_basic_2019* || echo

clean-shared:
	ipcrm -a
	ipcrm -m XXX
