#!/usr/bin/python3

import os
import sys
import executor
import signal
import argparse


def handler(signo, strakframe):
    print("Aborting....")
    executor.SHUTDOWN = True


def main():

    parser = argparse.ArgumentParser(
        description='fuzzing + concolic = fuzzolic :)')
    # optional args start with "-" for argparse
    parser.add_argument('--debug', action='store_true', help='enable debug mode')
    parser.add_argument('--version', action='version', version='%(prog)s pre-{\\alpha}^{\infty}')
    # positional args
    parser.add_argument('seed', metavar='<seed>', type=str, help='path to the initial seed')
    parser.add_argument('binary', metavar='<binary>', type=str, help='path to the binary to run')
    parser.add_argument('args', metavar='<args>', type=str, help='args for to the binary to run',
                        nargs='*')  # argparse.REMAINDER
    args = parser.parse_args()

    binary = args.binary
    if not os.path.exists(binary):
        sys.exit('ERROR: invalid binary')

    seed = args.seed
    if not os.path.exists(seed):
        sys.exit('ERROR: invalid seed')

    binary_args = args.args
    debug = args.debug

    signal.signal(signal.SIGINT, handler)

    fuzzolic_executor = executor.Executor(binary, seed, os.getcwd(), binary_args, debug)
    fuzzolic_executor.run()


if __name__ == "__main__":
    main()
