#!/usr/bin/python2.7

import os
import sys
import executor

if __name__ == "__main__":

    if len(sys.argv) != 3:
        print 'Usage: ' + sys.argv[0] + ' <binary> <seed>'
        sys.exit(1)

    binary = sys.argv[1]
    if not os.path.exists(binary):
        print 'ERROR: invalid binary'
        sys.exit(1)

    binary = sys.argv[1]
    if not os.path.exists(binary):
        print 'ERROR: invalid binary'
        sys.exit(1)

    seed = sys.argv[2]
    if not os.path.exists(seed):
        print 'ERROR: invalid seed'
        sys.exit(1)

    fuzzolic_executor = executor.Executor(binary, seed, "./")
    fuzzolic_executor.run()
