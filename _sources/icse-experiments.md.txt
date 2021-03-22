# ICSE Experiments

## SMT queries used in Section V-A

We executed the experiments in Section IV-A using the following:
* [queries](https://drive.google.com/file/d/1aTBMcWr6pzPNkVyJQnHqpxi2_xz8qgeu/view?usp=sharing)
* [queries splitted](https://drive.google.com/file/d/1MirAWRtEZmDubAsQrAUW62Woi5hnCwCy/view?usp=sharing)
* [seeds](https://drive.google.com/file/d/1x9da_dbbaI6DOPScbWzfl5K_WzStLy3L/view?usp=sharing)

**NOTE:** The queries in *queries* and *queries_splitted* are exactly the same, but in the former each query resides in a single file.

We collected the queries using QSYM by dumping the branch conditions of each benchmark when executed on a seed input (see Table below). In particular, we dumped the path constraints when the execution reached the `Solver::negatePath` function. We also deactivated the query simplification in the `Solver::add` function.

This table summarizes the benchmarks:

| Benchmark | Seed               | Num. of Queries |
|-----------|--------------------|-----------------|
| advmng    | mappy.mng          | 1481            |
| advzip    | small_archive.zip  | 300             |
| bloaty    | small_exec.elf     | 2085            |
| bsdtar    | tar.tar            | 325             |
| djpeg     | not_kitty.jpg      | 1245            |
| jhead     | not_kitty.jpg      | 405             |
| libpng    | not_kitty.png      | 1673            |
| lodepng   | not_kitty.png      | 1531            |
| objdump   | small_exec.elf     | 992             |
| optipng   | not_kitty.png      | 1740            |
| readelf   | small_exec.elf     | 1055            |
| tcpdump   | small_capture.pcap | 409             |
| tiff2pdf  | not_kitty.tiff     | 3084            |

#### Fuzzy-SAT vs Z3 experiment

The [run_batch_fuzzy_z3.sh](https://github.com/season-lab/fuzzy-sat/blob/dev/scripts/run_batch_fuzzy_z3.sh) script can be used to run both `z3` and `fuzzy-solver` on the queries.

To use the script, download the [queries](https://drive.google.com/file/d/1aTBMcWr6pzPNkVyJQnHqpxi2_xz8qgeu/view?usp=sharing) and the [seeds](https://drive.google.com/file/d/1x9da_dbbaI6DOPScbWzfl5K_WzStLy3L/view?usp=sharing), extract them, set accordingly `QUERIES_PATH`, `SEED_PATH` and `OUTPUT_DIR` in the script, and run it. It will create two CSV files for for each benchmark. The script [parse_info_query_splitted.py](https://github.com/season-lab/fuzzy-sat/blob/dev/scripts/parse_info_query_splitted.py) can be used to parse these CSV files and print a table about the number of queries proved sat by Fuzzy-SAT and Z3, and the elapsed time.

#### Fuzzy-SAT vs JSF experiment

This experiment can be executed similarly to the previous one, but you need to download [queries splitted](https://drive.google.com/file/d/1MirAWRtEZmDubAsQrAUW62Woi5hnCwCy/view?usp=sharing), use the [run_batch_fuzzy_jfs.sh](https://github.com/season-lab/fuzzy-sat/blob/master/scripts/run_batch_fuzzy_jfs.sh) to run the actual experiment, and parse the results using [parse_fuzzy_jfs.py](https://github.com/season-lab/fuzzy-sat/blob/master/scripts/parse_fuzzy_jfs.py).

## Configurations for benchmarks in Section V-C

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
		
