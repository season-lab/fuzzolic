#!/usr/bin/env python3

import os
import sys
import glob
import subprocess
import tempfile
import shutil

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
TRACER_BIN = SCRIPT_DIR + '/../tracer/x86_64-linux-user/qemu-x86_64'


def file_lines_count(fname):
    p = subprocess.Popen(['wc', '-l', fname], stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE)
    result, err = p.communicate()
    if p.returncode != 0:
        raise IOError(err)
    return int(result.strip().split()[0])


class TestcaseMinimizer(object):
    def __init__(self, cmd, global_bitmap):
        self.cmd = cmd
        self.use_stdin = False if "@@" in cmd else True
        self.global_bitmap = global_bitmap
        self.global_bitmap_pre_run = [None, None]

    def run(self, args, env, testcase, arg_input_idx):
        if self.use_stdin:
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

    def check_testcase(self, testcase, global_bitmap_pre_run, no_msg=False):

        # print("Testcase: %s" % testcase)

        if global_bitmap_pre_run != self.global_bitmap_pre_run[0]:
            self.cleanup()
            fp, bitmap = tempfile.mkstemp()
            os.close(fp)
            os.system("cp " + global_bitmap_pre_run + " " + bitmap)
            self.global_bitmap_pre_run = [global_bitmap_pre_run, bitmap]

        args = self.cmd
        args = [TRACER_BIN] + ['-symbolic'] + args
        arg_input_idx = -1
        if "@@" in args:
            assert not self.use_stdin
            arg_input_idx = args.index("@@")

        is_interesting = False

        env = os.environ.copy()
        env['COVERAGE_TRACER_FILTER_LIB'] = "-1"

        # compare against the bitmap before running the trace
        # this is for decting false positive
        fp, initial_global_bitmap = tempfile.mkstemp()
        os.close(fp)
        os.system("cp " + global_bitmap_pre_run + " " + initial_global_bitmap)
        env['COVERAGE_TRACER'] = initial_global_bitmap

        fp, coverage_log_path = tempfile.mkstemp()
        os.close(fp)
        env['COVERAGE_TRACER_LOG'] = coverage_log_path

        self.run(args, env, testcase, arg_input_idx)

        delta_coverage = file_lines_count(coverage_log_path)
        if delta_coverage == 0:
            if not no_msg:
                print("[-] Discarding %s" % os.path.basename(testcase))
                # print("WARNING: false positive?")
            is_interesting = False
        else:
            # compare against the bitmap after running the trace
            # we may have generated testcases that reach
            # similar basic blocks. We don't use the global
            # bitmap because the solver has already marked
            # solved branches as visited.
            env['COVERAGE_TRACER'] = self.global_bitmap_pre_run[1]

            os.unlink(coverage_log_path)
            fp, coverage_log_path = tempfile.mkstemp()
            os.close(fp)
            env['COVERAGE_TRACER_LOG'] = coverage_log_path

            self.run(args, env, testcase, arg_input_idx)

            initial_delta_coverage = delta_coverage
            delta_coverage = file_lines_count(coverage_log_path)
            if delta_coverage == 0:
                if not no_msg:
                    print("[=] Discarding %s (+%s, +0)" % (os.path.basename(testcase), initial_delta_coverage))
                is_interesting = False
            else:
                if not no_msg:
                    print("[+] Keeping %s (+%s, +%s)" %
                          (os.path.basename(testcase), initial_delta_coverage, delta_coverage))
                is_interesting = True

                # update global bitmap
                env['COVERAGE_TRACER'] = self.global_bitmap
                self.run(args, env, testcase, arg_input_idx)

        os.unlink(initial_global_bitmap)
        os.unlink(coverage_log_path)
        return is_interesting

    def cleanup(self):
        if self.global_bitmap_pre_run[1]:
            os.unlink(self.global_bitmap_pre_run[1])
