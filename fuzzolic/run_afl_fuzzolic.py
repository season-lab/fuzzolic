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

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
AFL_DIR = SCRIPT_DIR + '/../../AFLplusplus/'
AFL_BIN = AFL_DIR + '/afl-fuzz'
FUZZOLIC_BIN = SCRIPT_DIR + '/fuzzolic.py'
DEVNULL = open(os.devnull, 'w')

def handler(signo, stackframe):
    print("Aborting....")
    global p_children
    for p in p_children:
        p.send_signal(signal.SIGINT)
    sys.exit(1)

if len(sys.argv) < 5:
    print("Usage: %s <output-dir> <seed_dir> [<afl_args> ...] -- <program> <args>" % sys.argv[0])
    sys.exit(1)

run_dir = sys.argv[1]
input_dir = sys.argv[2]
afl_args = []
program_args = []

is_afl_args = True
for i in range(3, len(sys.argv)):
    arg = sys.argv[i]
    if arg == '--':
        is_afl_args = False
        continue
    if is_afl_args:
        afl_args.append(arg)
    else:
        program_args.append(arg)

if not os.path.exists(input_dir):
    print("Seed directory %s does not exist." % input_dir)
    sys.exit(1)

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

p_children = []
signal.signal(signal.SIGINT, handler)
signal.signal(signal.SIGTERM, handler)

if not debug:
    afl_master_args = [ AFL_BIN, '-c', '0', '-Q', '-M', 'afl-master', '-o', run_dir, '-i', input_dir] + afl_args + ['--'] + program_args
    afl_master = subprocess.Popen(afl_master_args, stdout=DEVNULL, stderr=DEVNULL)
    p_children.append(afl_master)

    afl_slave_args = [ AFL_BIN,'-Q', '-S', 'afl-slave', '-o', run_dir, '-i', input_dir] + afl_args + ['--'] + program_args
    afl_slave = subprocess.Popen(afl_slave_args, stdout=DEVNULL, stderr=DEVNULL)
    p_children.append(afl_slave)

    # print(' '.join(afl_slave_args))

    # wait for afl slave to create the bitmap
    time.sleep(30) #

filename = None
if '-e' in afl_args:
    filename = afl_args[afl_args.index('-e') + 1]

fuzzolic_args  = [ FUZZOLIC_BIN ]
if "FUZZY_SOLVER" in os.environ:
    fuzzolic_args += ["-f"]
if "OPTIMISTIC_SOLVING" in os.environ:
    fuzzolic_args += ["-p"]
if "USE_ADDRESS_REASONING" in os.environ:
    fuzzolic_args += ["-r"]
if "USE_MEMORY_SLICE" in os.environ:
    fuzzolic_args += ["-s"]
if "SOLVING_TIMEOUT" in os.environ:
    fuzzolic_args += ["-t", os.environ["SOLVING_TIMEOUT"]]
if filename:
    fuzzolic_args += ["-n", filename]
if "USE_MODELS" in os.environ:
    fuzzolic_args += ["-l"]
    print("Enabling lib models")

fuzzolic_args += [ '-a', run_dir + '/afl-slave/', '-i', run_dir + '/afl-slave/queue/', '-o', run_dir + '/fuzzolic', '--'] + program_args
fuzzolic = subprocess.Popen(fuzzolic_args, stdout=None, stderr=None)
p_children.append(fuzzolic)

for p in p_children:
    p.wait()
