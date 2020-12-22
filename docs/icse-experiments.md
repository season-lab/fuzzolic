# ICSE Experiments

## SMT queries used in Section IV-A

## Configurations for benchmarks in Section IV-C

| Benchmark | Release | Args | Seed | Dictionary | Driver |
|---|---|---|---|---|---|
| advmng | [advancecomp-2.0](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `-l @@` | [mappy.mng](https://github.com/amadvance/advancecomp/blob/master/test/mappy.mng) | | |
| advzip | [advancecomp-2.0](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `-l @@` | [small_archive.zip](https://github.com/google/AFL/blob/master/testcases/archives/common/zip/small_archive.zip) | | |
| bloaty | [1.0 git 7c6fc](https://github.com/google/bloaty/tree/7cf6c58688ca756147896d7bc2aaf96988e45d3b) | `@@` | [small_exec.elf](https://github.com/google/AFL/blob/master/testcases/others/elf/small_exec.elf) | | |
| bsdtar | [libarchive git f3b1f9](https://github.com/libarchive/libarchive/tree/f3b1f9f239c580b38f4d1197a40c6dde9753672e) | `tf @@` | [tar.tar](https://github.com/mathiasbynens/small/blob/master/tar.tar) | | |
| djpeg | [v9d](http://www.ijg.org/files/jpegsrc.v9d.tar.gz) | `@@` | [not_kitty.jpg](https://github.com/google/AFL/blob/master/testcases/images/jpeg/not_kitty.jpg) | [jpeg.dict](https://github.com/google/AFL/blob/master/dictionaries/jpeg.dict) | |
| jhead | [3.00-5](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `@@` | [not_kitty.jpg](https://github.com/google/AFL/blob/master/testcases/images/jpeg/not_kitty.jpg) | | |
| libpng | [1.6.37](https://sourceforge.net/projects/libpng/files/libpng16/1.6.37/) | `@@ /dev/null` | [not_kitty.png](https://github.com/google/AFL/blob/master/testcases/images/png/not_kitty.png) | [png.dict](https://github.com/google/AFL/blob/master/dictionaries/png.dict) | [driver.c](https://sites.cs.ucsb.edu/~pconrad/cs32/15F/lect/11.25/libpngCpp/libpngExample1.cpp) |
| lodepng | [20200112](https://lodev.org/lodepng/) | `@@` | [not_kitty.png](https://github.com/google/AFL/blob/master/testcases/images/png/not_kitty.png) | [png.dict](https://github.com/google/AFL/blob/master/dictionaries/png.dict) | |
| objdump | [binutils-2.34](https://ftp.gnu.org/gnu/binutils/binutils-2.34.tar.gz) | `-d @@` | [small_exec.elf](https://github.com/google/AFL/blob/master/testcases/others/elf/small_exec.elf) | | |
| optipng | [0.7.6](https://github.com/SoftSec-KAIST/Eclipser-Artifact/tree/master/docker-scripts/setup-scripts/packages-src) | `-out /dev/null @@` | [not_kitty.png](https://github.com/google/AFL/blob/master/testcases/images/png/not_kitty.png) | | |
| readelf | [binutils-2.34](https://ftp.gnu.org/gnu/binutils/binutils-2.34.tar.gz) | `-a @@` | [small_exec.elf](https://github.com/google/AFL/blob/master/testcases/others/elf/small_exec.elf) | | |
| tcpdump | [4.9.3](https://www.tcpdump.org/release/tcpdump-4.9.3.tar.gz) ([pcap 1.9.1](https://www.tcpdump.org/release/libpcap-1.9.1.tar.gz)) | `-e -vv -nr @@` | [small_capture.pcap](https://github.com/google/AFL/blob/master/testcases/others/pcap/small_capture.pcap) | | |
| tiff2pdf | [4.1.0](https://download.osgeo.org/libtiff/tiff-4.1.0.tar.gz) | `@@` | [not_kitty.tiff](https://github.com/google/AFL/blob/master/testcases/images/tiff/not_kitty.tiff) | [tiff.dict](https://github.com/google/AFL/blob/master/dictionaries/tiff.dict) | |


**NOTE #1**: CRC checks were disabled in lodepng.  
**NOTE #2**: When a benchmark is a library, we compiled it as a static library.
		
