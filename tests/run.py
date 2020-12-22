#!/usr/bin/python3

import os
import sys
import subprocess
import glob
import filecmp
import time

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
WORKDIR = SCRIPT_DIR + "/workdir"


def run(test, use_duplicate_testcase_checker=False, expected_inputs=1, perf_run=False, match_output=False, use_lib_models=False):
    initial_input = "%s/%s_0.dat" % (SCRIPT_DIR, test)
    assert os.path.exists(initial_input)

    env = os.environ.copy()
    if use_duplicate_testcase_checker:
        env['USE_DUPLICATE_TESTCASE_CHECKER'] = '1'

    native_time = None
    perf_run_opts = []
    if perf_run:
        perf_run_opts = ['-d', 'out']
        start = time.time()
        p = subprocess.Popen(
                                [
                                    SCRIPT_DIR + "/driver", test
                                ],
                                stderr=subprocess.DEVNULL,
                                stdin=subprocess.PIPE,
                                env=env
                            )
        with open(initial_input, "rb") as f:
            p.stdin.write(f.read())
            p.stdin.close()
        p.wait()
        end = time.time()
        native_time = end - start

    use_lib_opts = []
    if use_lib_models:
        use_lib_opts = ['-l']

    start = time.time()
    p = subprocess.Popen(
                            [
                                SCRIPT_DIR + "/../fuzzolic/fuzzolic.py",
                                "-o", WORKDIR,
                                "-i", initial_input,
                                "-k",
                            ] 
                            + perf_run_opts 
                            + use_lib_opts
                            + [
                                SCRIPT_DIR + "/driver", test
                            ],
                            stderr=subprocess.DEVNULL,
                            stdin=subprocess.DEVNULL,
                            env=env
                        )
    p.wait()
    end = time.time()
    emulated_time = end - start

    if perf_run:
        slowdown = emulated_time / native_time
        print("Slowdown: %s" % round(slowdown, 1))
        assert slowdown < 50

    testcases = glob.glob(WORKDIR + "/tests/test_*.dat") 
    assert len(testcases) == expected_inputs

    match = False

    if match_output:
        for f in testcases:
            p = subprocess.Popen(
                                    [
                                        SCRIPT_DIR + "/driver", test
                                    ],
                                    stderr=subprocess.DEVNULL,
                                    stdin=subprocess.PIPE,
                                    stdout=subprocess.PIPE,
                                    env=env
                                )
            with open(f, "rb") as fp:
                p.stdin.write(fp.read())
                #p.stdin.close()
            stdout = p.communicate()[0].decode("utf-8") 
            if stdout == 'RESULT=1\n':
                match = True
    else:
        expected_input = "%s/%s_1.dat" % (SCRIPT_DIR, test)
        assert os.path.exists(expected_input)
        for f in testcases:
            if filecmp.cmp(f, expected_input, shallow=False):
                match = True

    assert match


def test_simple_if():
    run("simple_if")


def test_nested_if():
    run("nested_if", expected_inputs=4)


def test_mystrcmp():
    # FixMe: to generate the correct input, we have to: 
    #   (1) disable bitmap filtering
    #   (2) start with a seed with enough bytes
    run("mystrcmp", use_duplicate_testcase_checker=True, expected_inputs=8)


def test_all_concrete():
    # performance test
    run("all_concrete", use_duplicate_testcase_checker=False, expected_inputs=1, perf_run=True)


def test_div3():
    run("div3", expected_inputs=1)


def test_addq():
    run("addq", expected_inputs=1, match_output=True)


def test_addl():
    run("addl", expected_inputs=1, match_output=True)


def test_addw():
    run("addw", expected_inputs=1, match_output=True)


def test_addb():
    run("addb", expected_inputs=1, match_output=True)


def test_adcq():
    run("adcq", expected_inputs=1, match_output=True)


def test_adcl():
    run("adcl", expected_inputs=1, match_output=True)


def test_adcw():
    run("adcw", expected_inputs=1, match_output=True)


def test_adcb():
    run("adcb", expected_inputs=1, match_output=True)


def test_model_strcmp():
    # FixMe: this models does not extend the input
    run("model_strcmp", expected_inputs=1, match_output=True, use_lib_models=True)