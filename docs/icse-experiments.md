# ICSE Experiments

## SMT queries used in Section IVA

## Configurations for benchmarks in Section IVC

| Benchmark | Release | Args | Seed | Driver | Dictionary |
|---|---|---|---|---|---|
| advmng | [advancecomp-2.0](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `-l @@` | [mappy.mng](https://github.com/amadvance/advancecomp/blob/master/test/mappy.mng) | | |
| advzip | [advancecomp-2.0](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `-l @@` | [small_archive.zip](https://github.com/google/AFL/blob/master/testcases/archives/common/zip/small_archive.zip) | | |
| bloaty | [1.0 git 7c6fc](https://github.com/google/bloaty/tree/7cf6c58688ca756147896d7bc2aaf96988e45d3b) | `@@` | [small_exec.elf](https://github.com/google/AFL/blob/master/testcases/others/elf/small_exec.elf) | | |
| bsdtar | [libarchive git f3b1f9](https://github.com/libarchive/libarchive/tree/f3b1f9f239c580b38f4d1197a40c6dde9753672e) | `tf @@` | [tar.tar](https://github.com/mathiasbynens/small/blob/master/tar.tar) | | |
| djpeg | [v9d](http://www.ijg.org/files/jpegsrc.v9d.tar.gz) | `@@` | [not_kitty.jpg](https://github.com/google/AFL/blob/master/testcases/images/jpeg/not_kitty.jpg) | | [jpeg.dict](https://github.com/google/AFL/blob/master/dictionaries/jpeg.dict) |
| jhead | [3.00-5](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `@@` | [not_kitty.jpg](https://github.com/google/AFL/blob/master/testcases/images/jpeg/not_kitty.jpg) | | |
| libpng | [1.6.37](https://sourceforge.net/projects/libpng/files/libpng16/1.6.37/) | `@@ /dev/null` | [not_kitty.jpg](https://github.com/google/AFL/blob/master/testcases/images/png/not_kitty.png) | [png.dict](https://github.com/google/AFL/blob/master/dictionaries/png.dict) | [driver.c](https://sites.cs.ucsb.edu/~pconrad/cs32/15F/lect/11.25/libpngCpp/libpngExample1.cpp) |
	
		
