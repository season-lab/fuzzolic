#!/usr/bin/python3

import os
import sys
import executor
import signal
import argparse
import shutil

ABORTING_COUNT = 0


def handler(signo, stackframe):
    print("[FUZZOLIC] Aborting....")
    executor.SHUTDOWN = True

    global ABORTING_COUNT
    ABORTING_COUNT += 1
    # if ABORTING_COUNT >= 3:
    #    sys.exit("Killing fuzzolic without cleanup. Not good.")


def main():

    parser = argparse.ArgumentParser(
        description='fuzzing + concolic = fuzzolic :)')

    # version
    parser.add_argument('--version', action='version',
                        version='%(prog)s pre-{\\alpha}^{\infty}')

    # optional args
    parser.add_argument(
        '-d', '--debug', choices=['gdb', 'trace', 'out', 'no_solver'], help='enable debug mode')
    parser.add_argument(
        '-a', '--afl', help='path to afl workdir')

    # required args
    parser.add_argument(
        '-i', '--input', help='path to the initial seed (or seed directory)', required=True)
    parser.add_argument(
        '-o', '--output', help='output directory', required=True)

    # positional args
    parser.add_argument('binary', metavar='<binary>',
                        type=str, help='path to the binary to run')
    parser.add_argument('args', metavar='<args>', type=str, help='args for to the binary to run',
                        nargs='*')  # argparse.REMAINDER

    args = parser.parse_args()

    binary = args.binary
    if not os.path.exists(binary):
        sys.exit('ERROR: binary does not exist.')

    input = args.input
    if not os.path.exists(input):
        sys.exit('ERROR: input does not exist.')

    output_dir = args.output
    if os.path.exists(output_dir):
        if os.path.exists(output_dir + '/.fuzzolic_workdir'):
            shutil.rmtree(output_dir)
        else:
            sys.exit("Unsafe to remove %s. Do it manually." % output_dir)
    if not os.path.exists(output_dir):
        os.system("mkdir -p " + output_dir)
        if not os.path.exists(output_dir):
            sys.exit('ERROR: cannot create output directory.')
        os.system("touch " + output_dir + '/.fuzzolic_workdir')

    if args.afl and not os.path.exists(args.afl):
        sys.exit('ERROR: AFL wordir does not exist.')
    afl = args.afl

    binary_args = args.args
    debug = args.debug

    signal.signal(signal.SIGINT, handler)

    fuzzolic_executor = executor.Executor(
        binary, input, output_dir, binary_args, debug, afl)
    fuzzolic_executor.run()


if __name__ == "__main__":
    main()
