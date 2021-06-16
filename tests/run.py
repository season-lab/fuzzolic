#!/usr/bin/python3

import os
import sys
import subprocess
import glob
import filecmp
import time
import pytest

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
WORKDIR = SCRIPT_DIR + "/workdir"


def pytest_addoption(parser):
    parser.addoption("--fuzzy", action="store_true", default="run tests using Fuzzy-SAT")


def run(test, 
        use_duplicate_testcase_checker=False, 
        expected_inputs=1, 
        perf_run=False, 
        match_output=False, 
        use_lib_models=False, 
        use_fuzzy=False,
        use_memory_slice=False,
        use_address_reasoning=False):

    initial_input = "%s/%s_0.dat" % (SCRIPT_DIR, test)
    assert os.path.exists(initial_input)

    env = os.environ.copy()
    if use_duplicate_testcase_checker:
        env['USE_DUPLICATE_TESTCASE_CHECKER'] = '1'

    native_time = None
    if perf_run:
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

    start = time.time()
    p = subprocess.Popen(
                            [
                                SCRIPT_DIR + "/../fuzzolic/fuzzolic.py",
                                "-o", WORKDIR,
                                "-i", initial_input,
                                "-k",
                            ] 
                            + (['-d', 'out'] if perf_run else []) 
                            + (['-l'] if use_lib_models else [])
                            + (['-f'] if use_fuzzy else [])
                            + (['-s'] if use_memory_slice else [])
                            + (['-r'] if use_address_reasoning else [])
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
        assert slowdown < 70

    if expected_inputs > 0:
        testcases = glob.glob(WORKDIR + "/tests/test_*.dat") 
        assert len(testcases) == expected_inputs
    else:
        testcases = glob.glob(WORKDIR + "/fuzzolic-00000/test_*.dat")

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


def test_simple_if(fuzzy):
    run("simple_if", use_fuzzy=fuzzy)


def test_nested_if(fuzzy):
    run("nested_if", expected_inputs=4, use_fuzzy=fuzzy)


def test_mystrcmp(fuzzy):
    # FixMe: to generate the correct input, we have to: 
    #   (1) disable bitmap filtering
    #   (2) start with a seed with enough bytes
    run("mystrcmp", use_duplicate_testcase_checker=True, expected_inputs=8, use_fuzzy=fuzzy)


def test_all_concrete(fuzzy):
    # performance test
    run("all_concrete", use_duplicate_testcase_checker=False, expected_inputs=1, perf_run=True, use_fuzzy=fuzzy)


def test_div3(fuzzy):
    if fuzzy:
        pytest.skip("Fuzzy-SAT cannot deterministically solve this")
    run("div3", expected_inputs=1)


def test_addq(fuzzy):
    run("addq", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_addl(fuzzy):
    run("addl", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_addw(fuzzy):
    run("addw", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_addb(fuzzy):
    run("addb", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_adcq(fuzzy):
    run("adcq", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_adcl(fuzzy):
    run("adcl", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_adcw(fuzzy):
    run("adcw", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_adcb(fuzzy):
    run("adcb", expected_inputs=1, match_output=True, use_fuzzy=fuzzy)


def test_model_strcmp(fuzzy):
    run("model_strcmp", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_strncmp(fuzzy):
    run("model_strncmp", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_strlen(fuzzy):
    run("model_strlen", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_strnlen_v0(fuzzy):
    run("model_strnlen_v0", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_strnlen_v1(fuzzy):
    run("model_strnlen_v1", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_memcmp_v0(fuzzy):
    run("model_memcmp_v0", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_memcmp_v1(fuzzy):
    run("model_memcmp_v1", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_memchr(fuzzy):
    run("model_memchr", expected_inputs=1, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_symbolic_index(fuzzy):
    pytest.skip("This test requires to build the tracer with memory slice support")
    run("symbolic_index", expected_inputs=1, use_fuzzy=fuzzy, use_memory_slice=True)


def test_symbolic_read(fuzzy):
    run("symbolic_read", expected_inputs=2, match_output=True, use_fuzzy=fuzzy, use_memory_slice=True)


def test_switch(fuzzy):
    pytest.skip("This test requires to build the tracer with memory slice support")
    run("switch", expected_inputs=7, match_output=True, use_fuzzy=fuzzy, use_address_reasoning=True)


def test_model_malloc_min(fuzzy):
    run("model_malloc_min", expected_inputs=0, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_malloc_max(fuzzy):
    run("model_malloc_max", expected_inputs=0, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_realloc_min(fuzzy):
    run("model_realloc_min", expected_inputs=0, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)


def test_model_realloc_max(fuzzy):
    run("model_realloc_max", expected_inputs=0, match_output=True, use_lib_models=True, use_fuzzy=fuzzy)
