#!/usr/bin/python2.7

import os
import sys
import glob


def main():
    if len(sys.argv) != 2:
        print "Usage " + sys.argv[0] + " <fuzzolic_working_dir>"
        sys.exit(1)

    working_dir = sys.argv[1]
    if not os.path.exists(working_dir):
        print "Invalid working director."
        sys.exit(1)

    files = list(filter(os.path.isfile, glob.glob(
        working_dir + "/tests/test_case_*.dat")))
    files.sort(key=lambda x: os.path.getmtime(x))

    for f in files:
        print("\nTest case: " + f)
        os.system("xxd " + f)


if __name__ == "__main__":
    main()
