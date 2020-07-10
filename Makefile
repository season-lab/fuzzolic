COUNT=3850

all: build clean-work-dir
	./fuzzolic/fuzzolic.py -o workdir -i tests/simple_if_0.dat tests/driver simple_if
	./utils/print_test_cases.py workdir/tests

fuzzy: build clean-work-dir
	./fuzzolic/fuzzolic.py -f -o workdir -i tests/simple_if_0.dat tests/driver simple_if
	./utils/print_test_cases.py workdir/tests

simpleif: build-tracer build-solver kill-solver clean-work-dir
	time -p ./fuzzolic/fuzzolic.py --debug out -o workdir -i tests/simple_if_0.dat tests/driver simple_if
	./utils/print_test_cases.py workdir/tests

native:
	cat tests/simple_if_input_ko.dat | ./tracer/x86_64-linux-user/qemu-x86_64 -d in_asm,op_opt,out_asm ./tests/simple-if 2> asm_in_out.log

all-concrete: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py --debug out -o workdir -i tests/all_concrete_0.dat tests/driver all_concrete
	./utils/print_test_cases.py workdir/tests

all-concrete-full: build-tracer build-solver kill-solver clean-work-dir
	time -p ./fuzzolic/fuzzolic.py -o workdir -i tests/all_concrete_0.dat tests/driver all_concrete
	./utils/print_test_cases.py workdir/tests

strcmp-debug: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py --debug out tests/strcmp_d.dat tests/strcmp
	./utils/print_test_cases.py workdir/tests

strcmp: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py tests/strcmp_ko.dat tests/strcmp
	./utils/print_test_cases.py workdir/tests

mystrcmp: clean-work-dir kill-solver
	time -p ./fuzzolic/fuzzolic.py -o workdir -i tests/mystrcmp_0.dat tests/driver mystrcmp
	./utils/print_test_cases.py workdir/tests

configure:
	cd tracer && ./configure --target-list=i386-linux-user,x86_64-linux-user # --disable-werror

clean-work-dir:
	rm -rf workdir

kill-solver:
	killall -SIGINT solver || echo "No solver still alive to kill"

build: build-solver build-tracer
	echo "Built."

build-solver:
	cd solver && make

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

lodepng:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/lodepng/seeds/not_kitty.png -- ../fuzzolic-evaluation/benchmarks/lodepng/lodepng_decode_cg_nocksm @@

lodepng-fuzzy:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/lodepng/seeds/not_kitty.png -f -l -- ../fuzzolic-evaluation/benchmarks/lodepng/lodepng_decode_cg_nocksm @@

djpeg:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/djpeg/seeds/not_kitty.jpg -- ../fuzzolic-evaluation/benchmarks/djpeg/djpeg @@

djpeg-fuzzy:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/djpeg/seeds/not_kitty.jpg -f -- ../fuzzolic-evaluation/benchmarks/djpeg/djpeg @@

bloaty:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/bloaty/seeds/small_exec.elf -- ../fuzzolic-evaluation/benchmarks/bloaty/bloaty @@

bloaty-fuzzy:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/bloaty/seeds/small_exec.elf -f -- ../fuzzolic-evaluation/benchmarks/bloaty/bloaty @@

readelf:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/readelf/seeds/small_exec.elf -- ../fuzzolic-evaluation/benchmarks/readelf/readelf_nopie -a @@

readelf-fuzzy:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/readelf/seeds/small_exec.elf -f  -- ../fuzzolic-evaluation/benchmarks/readelf/readelf_nopie -a @@

wavpack:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/wavpack/seeds/int32.wav -n input.wav -- ../fuzzolic-evaluation/benchmarks/wavpack/wavpack -y @@ -o /dev/shm/tmp

wavpack-fuzzy:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/wavpack/seeds/int32.wav -n input.wav -f -- ../fuzzolic-evaluation/benchmarks/wavpack/wavpack -y @@ -o /dev/shm/tmp

objdump:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/objdump/seeds/small_exec.elf -- ../fuzzolic-evaluation/benchmarks/objdump/objdump -d @@

objdump-fuzzy:
	reset && make build && ./fuzzolic/fuzzolic.py -d out -o workdir -i ../fuzzolic-evaluation/benchmarks/objdump/seeds/small_exec.elf -f -- ../fuzzolic-evaluation/benchmarks/objdump/objdump -d @@
