#!/usr/bin/python3

import os
import sys
import glob
import subprocess
import tempfile
import shutil

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
TRACER_BIN = SCRIPT_DIR + "/fuzzolic_coverage_trace_bin"


def progressBar(value, endvalue, bar_length=20):

    percent = float(value) / endvalue
    arrow = '=' * int(round(percent * bar_length)-1) + '>'
    spaces = ' ' * (bar_length - len(arrow))

    # sys.stdout.write("\rPercent: [{0}] {1}%".format(arrow + spaces, int(round(percent * 100))))
    sys.stdout.write("\rProgress: [{0}] {1}/{2}".format(arrow + spaces, value, endvalue))
    sys.stdout.flush()


def file_lines_count(fname):
    p = subprocess.Popen(['wc', '-l', fname], stdout=subprocess.PIPE, 
                                              stderr=subprocess.PIPE)
    result, err = p.communicate()
    if p.returncode != 0:
        raise IOError(err)
    return int(result.strip().split()[0])


def usage():
    print("usage: %s {-l0,-l1} <fuzzer dir> -- ./binary [<args>]" % sys.argv[0])
    print("-l0: do not filter coverage from libraries")
    print("-l1: filter coverage from libraries")
    print("<args> can contain @@ in place of the testcase argument")
    print("<fuzzer dir> should contain {queue, crashes} directories")
    sys.exit(1)

if len(sys.argv) < 5:
    print("Too few arguments.")
    usage()

if sys.argv[1] not in ["-l0", "-l1"]:
    print("Invalid coverage filter argument.")
    usage()
filter_coverage_lib = True if sys.argv[1] == "-l1" else False

if sys.argv[3] != '--':
    print("Invalid command separator.")
    usage()

fuzzer_dir = sys.argv[2]
if not os.path.exists(fuzzer_dir):
    print("Invalid fuzzer directory.")
    usage()
fuzzer_dir = os.path.abspath(fuzzer_dir)

args = [TRACER_BIN] + ['-symbolic'] + sys.argv[4:]

use_stdin = True
arg_input_idx = -1
if "@@" in args:
    use_stdin = False
    arg_input_idx = args.index("@@")

testcase_dirs = []
if os.path.exists(fuzzer_dir + "/queue"):
    testcase_dirs.append(fuzzer_dir + "/queue")
if os.path.exists(fuzzer_dir + "/crash"):
    testcase_dirs.append(fuzzer_dir + "/crash")

if len(testcase_dirs) == 0:
    print("No known directory inside %s" % fuzzer_dir)
    usage()

coverage_bitmap, coverage_bitmap_path = tempfile.mkstemp()
coverage_log, coverage_log_path = tempfile.mkstemp()

# workdir = tempfile.mkdtemp()
# os.system("touch " + workdir + "/.fuzzolic_workdir")

env = os.environ.copy()
env['COVERAGE_TRACER'] = coverage_bitmap_path
env['COVERAGE_TRACER_LOG'] = coverage_log_path
if filter_coverage_lib:
    print("Filtering out coverage from library code")
    env['COVERAGE_TRACER_FILTER_LIB'] = "1"

testcase_total = 0
for dir in testcase_dirs:
    for testcase in glob.glob(dir + "/*"):
        if testcase.startswith(".") or 'README' in testcase:
            continue
        testcase_total += 1

testcase_count = 0
for dir in testcase_dirs:
    for testcase in glob.glob(dir + "/*"):
        if testcase.startswith(".") or 'README' in testcase:
            continue

        # print("Running testcase %s" % testcase)
        progressBar(testcase_count, testcase_total, 80)
        testcase_count += 1

        if use_stdin:
            p = subprocess.Popen(args,
                                 stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL,
                                 stdin=subprocess.PIPE,
                                 env=env,
                                 #cwd=workdir
                                 )
            with open(testcase, "rb") as f:
                p.stdin.write(f.read())
            p.stdin.close()
            p.wait()
        else:
            args_new = args[:]
            args_new[arg_input_idx] = testcase
            p = subprocess.Popen(args_new,
                                 stdout=subprocess.DEVNULL,
                                 stderr=subprocess.DEVNULL,
                                 stdin=subprocess.PIPE,
                                 env=env,
                                 # cwd=workdir
                                 )
            p.stdin.close()
            p.wait()

progressBar(testcase_count, testcase_total, 80)

print("\n\nTotal number of basic blocks: %d" % file_lines_count(coverage_log_path))
print("Total number of processed testcases: %d\n" % testcase_count)

# if os.path.exists(workdir + '/.fuzzolic_workdir'):
#    shutil.rmtree(workdir)
os.unlink(coverage_bitmap_path)
os.unlink(coverage_log_path)

