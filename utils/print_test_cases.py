#!/usr/bin/python3

import os
import sys
import glob


def main():
    if len(sys.argv) != 2:
        sys.exit("Usage %s <fuzzolic_working_dir>" % sys.argv[0])

    working_dir = sys.argv[1]
    if not os.path.exists(working_dir):
        sys.exit("Invalid working director")

    files = list(filter(os.path.isfile,
                        glob.glob(working_dir + "/test_case_*.dat")))
    files.sort(key=lambda x: os.path.getmtime(x))

    for f in files:
        print("\nTest case: %s" % f)
        os.system("xxd " + f)


if __name__ == "__main__":
    main()
