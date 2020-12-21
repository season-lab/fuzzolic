#!/usr/bin/python3

import os
import sys
import subprocess
import glob
import filecmp

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
WORKDIR = SCRIPT_DIR + "/workdir"


def run(test, single_run=True, expected_inputs=1):
    initial_input = "%s/%s_0.dat" % (SCRIPT_DIR, test)
    assert os.path.exists(initial_input)
    expected_input = "%s/%s_1.dat" % (SCRIPT_DIR, test)
    assert os.path.exists(expected_input)

    p = subprocess.Popen(
                            [
                                SCRIPT_DIR + "/../fuzzolic/fuzzolic.py",
                                "-o", WORKDIR,
                                "-i", initial_input,
                                SCRIPT_DIR + "/driver", test
                            ],
                            stderr=subprocess.DEVNULL,
                            stdin=subprocess.DEVNULL,
                        )
    p.wait()

    testcases = glob.glob(WORKDIR + "/tests/test_*.dat") 
    assert len(testcases) == expected_inputs

    match = False    
    for f in testcases:
        if filecmp.cmp(f, expected_input, shallow=False):
            match = True

    assert match


def run_one(test, expected_inputs=1):
    run(test, single_run=True, expected_inputs=expected_inputs)


def test_simple_if():
    run_one("simple_if")


def test_nested_if():
    run_one("nested_if", expected_inputs=4)