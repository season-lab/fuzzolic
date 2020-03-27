#!/usr/bin/python3

import os
import sys
import glob
import filecmp

root_dir = sys.argv[1]

unique_inputs = []
for f in glob.glob(root_dir + "/*/*.dat"):
    is_unique = True
    for fu in unique_inputs:
        if filecmp.cmp(f, fu, shallow=False):
            is_unique = False
            print("%s is equal to %s" % (f, fu))
            break
    if is_unique:
        unique_inputs.append(f)

