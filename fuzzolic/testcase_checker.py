#!/usr/bin/python3

import os
import sys
import glob
import subprocess
import tempfile
import shutil

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
TRACER_BIN = SCRIPT_DIR + '/../tracer/x86_64-linux-user/qemu-x86_64'


def progressBar(value, endvalue, bar_length=20):

    percent = float(value) / endvalue
    arrow = '=' * int(round(percent * bar_length)-1) + '>'
    spaces = ' ' * (bar_length - len(arrow))

    # sys.stdout.write("\rPercent: [{0}] {1}%".format(arrow + spaces, int(round(percent * 100))))
    sys.stdout.write(
        "\rProgress: [{0}] {1}/{2}".format(arrow + spaces, value, endvalue))
    sys.stdout.flush()


def file_lines_count(fname):
    p = subprocess.Popen(['wc', '-l', fname], stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    result, err = p.communicate()
    if p.returncode != 0:
        raise IOError(err)
    return int(result.strip().split()[0])


def usage():
    print("usage: %s <testcase dir> <bitmap> -- ./binary [<args>]" % sys.argv[0])
    sys.exit(1)


def run(args, use_stdin, env, testcase):
    if use_stdin:
        p = subprocess.Popen(args,
                                stdout=subprocess.DEVNULL,
                                stderr=subprocess.DEVNULL,
                                stdin=subprocess.PIPE,
                                env=env,
                                # cwd=workdir
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

if len(sys.argv) < 5:
    print("Too few arguments.")
    usage()

if sys.argv[3] != '--':
    print("Invalid command separator.")
    usage()

testcase_dir = sys.argv[1]
if not os.path.exists(testcase_dir):
    print("Invalid testcase directory.")
    usage()
testcase_dir = os.path.abspath(testcase_dir)

args = [TRACER_BIN] + ['-symbolic'] + sys.argv[4:]

use_stdin = True
arg_input_idx = -1
if "@@" in args:
    use_stdin = False
    arg_input_idx = args.index("@@")

coverage_bitmap_path = sys.argv[2]
if not os.path.exists(coverage_bitmap_path):
    print("Invalid bitmap file.")
    usage()
coverage_bitmap_path = os.path.abspath(coverage_bitmap_path)

env = os.environ.copy()

env['COVERAGE_TRACER_FILTER_LIB'] = "-1"

_, coverage_bitmap_path_copy = tempfile.mkstemp()
os.system("cp " + coverage_bitmap_path + " " + coverage_bitmap_path_copy)

testcase_count = 0
for testcase in glob.glob(testcase_dir + "/test_case_*.dat"):
    if testcase.startswith(".") or 'README' in testcase:
        continue

    # print("Running testcase %s" % testcase)
    testcase_count += 1

    _, coverage_log_path = tempfile.mkstemp()
    _, coverage_bitmap_path_copy_run = tempfile.mkstemp()
    os.system("cp " + coverage_bitmap_path_copy + " " + coverage_bitmap_path_copy_run)
    env['COVERAGE_TRACER'] = coverage_bitmap_path_copy_run
    env['COVERAGE_TRACER_LOG'] = coverage_log_path

    run(args, use_stdin, env, testcase)

    delta_coverage = file_lines_count(coverage_log_path)
    if delta_coverage == 0:
        print("[-] %s %s" % (delta_coverage, os.path.basename(testcase)))
    else:

        env['COVERAGE_TRACER'] = coverage_bitmap_path
        os.unlink(coverage_log_path)
        _, coverage_log_path = tempfile.mkstemp()
        env['COVERAGE_TRACER_LOG'] = coverage_log_path

        run(args, use_stdin, env, testcase)

        delta_coverage = file_lines_count(coverage_log_path)
        if delta_coverage == 0:
            print("[ ] %s %s" % (delta_coverage, os.path.basename(testcase)))
        else:
            print("[+] %s %s" % (delta_coverage, os.path.basename(testcase)))

    os.unlink(coverage_log_path)
    os.unlink(coverage_bitmap_path_copy_run)
