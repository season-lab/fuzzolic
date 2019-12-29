#!/usr/bin/python2.7

import os
import sys

if __name__ == "__main__":
    DIR = os.path.dirname(os.path.realpath(__file__))

    if len(sys.argv) != 2:
        print 'Usage: ' + sys.argv[0] + ' <binary>'
        sys.exit(1)

    BINARY = sys.argv[1]
    if not os.path.exists(BINARY):
        print 'ERROR: invalid binary'
        sys.exit(1)

    cmd  = DIR + '/../solver/solver &'
    cmd += ' ' + DIR + '/../tracer/x86_64-linux-user/qemu-x86_64 -symbolic ' + sys.argv[1]
    cmd += ' && wait'

    os.system(cmd)
