#!/usr/bin/python3 -u

import os
import sys
import json
import glob
import subprocess
import time
import signal
import json
import shutil
import argparse

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))

if 'AFL_PATH' not in os.environ:
    AFL_PATH = SCRIPT_DIR + '/../../AFLplusplus/'
else:
    AFL_PATH = os.environ['AFL_PATH']

AFL_BIN = AFL_PATH + '/afl-fuzz'
FUZZOLIC_BIN = SCRIPT_DIR + '/fuzzolic.py'
DEVNULL = open(os.devnull, 'w')
WAITING_TIME_AFTER_AFL_INSTANCE_START = 30

p_children = []

def handler(signo, stackframe):
    print("Aborting....")
    global p_children
    for p in p_children:
        p.send_signal(signal.SIGINT)
    for p in p_children:
        try:
            p.wait(10)
        except:
            pass
    sys.exit(1)

def main():

    parser = argparse.ArgumentParser(
        description='fuzzolic + AFL')

    # version
    parser.add_argument('--version', action='version',
                        version='%(prog)s pre-{\\alpha}^{\infty}')

    parser.add_argument(
        '-g', '--afl-args', help='String containing additional args to use when launching AFL/AFL++. E.g., -g \'-m 2G\'')
    parser.add_argument(
        '-f', '--fuzzy', action='store_true', help='use Fuzzy-SAT solver in fuzzolic')
    parser.add_argument(
        '-r', '--address-reasoning', action='store_true', help='enable address reasoning')
    parser.add_argument(
        '-s', '--memory-slice', action='store_true', help='enable memory slice reasoning [experimental]')
    parser.add_argument(
        '-p', '--optimistic-solving', action='store_true', help='enable optimistic solving')
    parser.add_argument(
        '-t', '--timeout', type=int, help='set timeout on the solving time (ms)')
    parser.add_argument(
        '-l', '--symbolic-models', action='store_true', help='Enable symbolic models')
    parser.add_argument(
        '-k', '--keep-run-dirs', action='store_true', help='keep run directories')

    # required args
    parser.add_argument(
        '-o', '--output', help='output directory', required=True)
    parser.add_argument(
        '-i', '--input', help='path to the initial seed (or seed directory)', required=True)

    # positional args
    parser.add_argument('binary', metavar='<binary>',
                        type=str, help='path to the binary to run')
    parser.add_argument('args', metavar='<args>', type=str, help='args for to the binary to run',
                        nargs='*')  # argparse.REMAINDER

    args = parser.parse_args()

    run_dir = args.output
    input_dir = args.input
    if not os.path.exists(input_dir):
        print("Seed directory %s does not exist." % input_dir)
        sys.exit(1)
    
    afl_args = args.afl_args
    if afl_args is not None:
        if afl_args[0] == "'" or afl_args[0] == '"':
            afl_args = afl_args[1:]
        if afl_args[-1] == "'" or afl_args[-1] == '"':
            afl_args = afl_args[:-2] 
        afl_args = afl_args.split(" ")
    else:
        afl_args = []

    program_args = [ args.binary ] + args.args

    debug = False
    if "DEBUG_RUN" in os.environ:
        debug = True

    if not debug:
        if os.path.exists(run_dir):
            if os.path.exists(run_dir + '/.fuzzolic'):
                shutil.rmtree(run_dir)
            else:
                print("Unsafe to remove %s. Do it manually." % run_dir)
                sys.exit(1)

        os.system("mkdir %s" % run_dir)
        os.system("touch %s/%s " % (run_dir, '.fuzzolic'))

    signal.signal(signal.SIGINT, handler)
    signal.signal(signal.SIGTERM, handler)

    if not debug:

        prog = program_args[0]
        if os.path.exists(prog + "_afl"):
            prog = prog + "_afl"
            afl_args[afl_args.index("-m") + 1] = "none"
            red_queen_mode_a = "-c"
            red_queen_mode_b = prog
        else:
            afl_args.append("-Q")
            red_queen_mode_a = "-c"
            red_queen_mode_b = "0"

        afl_master_args = [ AFL_BIN, red_queen_mode_a, red_queen_mode_b, '-M', 'afl-master', '-o', run_dir, '-i', input_dir] + afl_args + ['--'] + [ prog ] + program_args[1:]
        afl_master = subprocess.Popen(afl_master_args, stdout=DEVNULL, stderr=DEVNULL)
        p_children.append(afl_master)
        print("Running: %s" % ' '.join(afl_master_args))

        print("Waiting %s seconds before starting slave." % WAITING_TIME_AFTER_AFL_INSTANCE_START)
        time.sleep(WAITING_TIME_AFTER_AFL_INSTANCE_START)

        afl_slave_args = [ AFL_BIN, '-S', 'afl-slave', '-o', run_dir, '-i', input_dir] + afl_args + [ prog ] + program_args[1:]
        afl_slave = subprocess.Popen(afl_slave_args, stdout=DEVNULL, stderr=DEVNULL)
        p_children.append(afl_slave)

        print("Running: %s" % ' '.join(afl_slave_args))

        # wait for afl slave to create the bitmap
        print("Waiting %s seconds before starting fuzzolic." % WAITING_TIME_AFTER_AFL_INSTANCE_START)
        time.sleep(WAITING_TIME_AFTER_AFL_INSTANCE_START)

    fuzzolic_args  = [ FUZZOLIC_BIN ]
    if '-e' in afl_args:
        filename = afl_args[afl_args.index('-e') + 1]
        fuzzolic_args += ["-n", filename]
    if args.fuzzy:
        fuzzolic_args += ["-f"]
    if args.optimistic_solving:
        fuzzolic_args += ["-p"]
    if args.address_reasoning:
        fuzzolic_args += ["-r"]
    if args.memory_slice:
        fuzzolic_args += ["-s"]
    if args.timeout:
        fuzzolic_args += ["-t", str(args.timeout)]
    if args.symbolic_models:
        fuzzolic_args += ["-l"]
    if args.keep_run_dirs:
        fuzzolic_args += ["-k"]

    fuzzolic_args += [ '-a', run_dir + '/afl-slave/', '-i', run_dir + '/afl-slave/queue/', '-o', run_dir + '/fuzzolic', '--'] + program_args
    fuzzolic = subprocess.Popen(fuzzolic_args, stdout=None, stderr=None)
    p_children.append(fuzzolic)

    print("Running: %s" % ' '.join(fuzzolic_args))

    for p in p_children:
        p.wait()


if __name__ == "__main__":
    main()