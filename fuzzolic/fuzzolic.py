#!/usr/bin/python3

import os
import sys
import executor
import signal


def handler(signo, strakframe):
    print("Aborting....")
    executor.SHUTDOWN = True

def main():

    signal.signal(signal.SIGINT, handler)

    if len(sys.argv) != 3:
        sys.exit('Usage: %s <binary> <seed>' % (sys.argv[0],))

    binary = sys.argv[1]
    if not os.path.exists(binary):
        sys.exit('ERROR: invalid binary')

    binary = sys.argv[1]
    if not os.path.exists(binary):
        sys.exit('ERROR: invalid binary')

    seed = sys.argv[2]
    if not os.path.exists(seed):
        sys.exit('ERROR: invalid seed')

    fuzzolic_executor = executor.Executor(binary, seed, os.getcwd())
    fuzzolic_executor.run()


if __name__ == "__main__":
    main()
