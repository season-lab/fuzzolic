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
AFL_DIR = SCRIPT_DIR + '/../../AFL/'
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
    afl_master_args = [ AFL_BIN, '-Q', '-M', 'afl-master', '-o', run_dir, '-i', input_dir] + afl_args + ['--'] + program_args
    afl_master = subprocess.Popen(afl_master_args, stdout=DEVNULL, stderr=DEVNULL)
    p_children.append(afl_master)

    afl_slave_args = [ AFL_BIN, '-Q', '-S', 'afl-slave', '-o', run_dir, '-i', input_dir] + afl_args + ['--'] + program_args
    afl_slave = subprocess.Popen(afl_slave_args, stdout=DEVNULL, stderr=DEVNULL)
    p_children.append(afl_slave)

    # wait for afl slave to create the bitmap
    time.sleep(20) #

fuzzy_args = []
if "FUZZY_SOLVER" in os.environ:
    fuzzy_args.append("-f")

fuzzolic_args  = [ FUZZOLIC_BIN ]
fuzzolic_args += fuzzy_args
fuzzolic_args += [ '-a', run_dir + '/afl-slave/', '-i', run_dir + '/afl-slave/queue/', '-o', run_dir + '/fuzzolic', '--'] + program_args
fuzzolic = subprocess.Popen(fuzzolic_args, stdout=None, stderr=None)
p_children.append(fuzzolic)

for p in p_children:
    p.wait()
