#!/usr/bin/python3 -u

import os
import sys
import subprocess
import argparse
import shutil
import signal
import z3
import glob
import struct
import random


SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
CHILDREN = []

def get_inputs(e):
    inputs = set()
    opkind = str(e.decl())
    #print(opkind)
    if opkind in ["bv", "True", "False"]:
        return inputs
    elif opkind.startswith("k!"):
        inputs.add(e)
        return inputs
    else:
        for k in range(e.num_args()):
            inputs |= get_inputs(e.arg(k))
        return inputs


def safe_dir_rm(path):
    if os.path.exists(path):
        if not os.path.exists(path + "/.fuzzolic_workdir"):
            print("Not safe to delete %s. Do it manually." % path)
            sys.exit(1)
        shutil.rmtree(path)


def handler(signo, stacktrace):
    global CHILDREN
    for p in CHILDREN:
        p.send_signal(signal.SIGINT)
        try:
            p.wait(10)
        except subprocess.TimeoutExpired:
            p.send_signal(signal.SIGKILL)
    sys.exit(0)


signal.signal(signal.SIGINT, handler)
signal.signal(signal.SIGTERM, handler)

parser = argparse.ArgumentParser()
parser.add_argument('--restart', action='store_true')
parser.add_argument('--index', type=int)
parser.add_argument('--timeout', type=int)
parser.add_argument('--output-dir', type=str, required=True)
parser.add_argument('--input', type=str, required=True)
parser.add_argument('binary', metavar='<binary>', type=str)
parser.add_argument('args', metavar='<args>', type=str, nargs='+')

args = parser.parse_args()

timeout = 0
if args.timeout:
    timeout = args.timeout

if not args.restart:
    safe_dir_rm(args.output_dir)

if not os.path.exists(args.output_dir):
    os.mkdir(args.output_dir)
    os.system("touch %s/.fuzzolic_workdir" % args.output_dir)

assert(os.path.exists(args.input))

p_args  = [ SCRIPT_DIR + "/fuzzolic.py"]
p_args += [ "-i",  args.input ]
p_args += [ "-o",  args.output_dir ]
p_args += [ "-k", "-l", "-d", "out" ]
p_args += [ "--" ]
p_args += [ args.binary ] + args.args

if not args.restart:
    p = subprocess.Popen(
                        p_args,
                        #stdout=subprocess.DEVNULL,
                        #stderr=subprocess.DEVNULL
                    )
    CHILDREN.append(p)

    if timeout > 0:
        try:
            p.wait(timeout)
        except subprocess.TimeoutExpired:
            p.send_signal(signal.SIGINT)
            try:
                p.wait(10)
            except subprocess.TimeoutExpired:
                p.send_signal(signal.SIGKILL)
    else:
        p.wait()

    CHILDREN = []

index = 0
if args.index:
    index = args.index

input_values = []
with open(args.input, "rb") as fp:
    v = fp.read(1)
    while v:
        v = struct.unpack("B", v)[0]
        input_values.append(v)
        #print(v)
        v = fp.read(1)
#print(input_values)

symbolic_queries = 0
processed_queries = 0
queries = glob.glob(args.output_dir + "/fuzzolic-0*/*.pi")
queries = sorted(queries, key=os.path.getmtime)
i = 0
for query in queries:
    expr_idx = query.rstrip(".pi").split("_")[-1]
    if args.index and int(expr_idx) < args.index:
        continue

    processed_queries += 1

    pi = z3.parse_smt2_file(query)
    expr = z3.parse_smt2_file(query.rstrip(".pi") + ".expr")
    if type(expr) is z3.z3.AstVector:
        assert len(expr) == 1
        expr = expr[0]
    
    assert(str(expr.decl()) == "==")
    expr = expr.arg(0)

    inputs = get_inputs(expr)

    # get solution for current testcase
    solver = z3.Solver()
    solver.add(pi)
    r = solver.check()
    assert(str(r) == "sat")

    # print("\n# [%d/%d] Analyzing debug query: %s" % (symbolic_queries, processed_queries, query.rstrip(".pi")))
    # print("Path constraints: %s" % pi)
    # print("Expression: %s" % expr)
    # print("Inputs: %s" % inputs)

    add_inputs = set()
    remove_inputs = set()
    while True:
        has_fake_input = False
        for input in inputs:
            index = int(str(input)[2:])
            if index >= len(input_values):
                found = False
                has_fake_input = True
                # print("Fake input %s %s" % (input, index))
                for c in pi.children():
                    if str(c.decl()) == "==" and str(c.arg(0).decl()) == "k!%s" % (index + 1):
                        add_inputs |= get_inputs(c.arg(1))
                        remove_inputs.add(input)
                        found = True
                        break
                    elif str(c.decl()) == "And":
                        for cc in c.children():
                            if str(cc.decl()) == "==" and str(cc.arg(0).decl()) == "k!%s" % (index + 1):
                                add_inputs |= get_inputs(cc.arg(1))
                                remove_inputs.add(input)
                                found = True
                                break
                    if found:
                        break
                if not found:
                    print("Fake input %s not found" % input)
                    print(pi)
                    print("##")
                    print(expr)
                    sys.exit(1)
        inputs |= add_inputs
        inputs -= remove_inputs
        # print("Inputs: %s" % inputs)
        if not has_fake_input:
            break

    real_inputs = 0
    for input in inputs:
        index = int(str(input)[2:])
        if index >= len(input_values):
            continue
        real_inputs += 1
        value = input_values[index]
        solver.add(input == z3.BitVecVal(value, 8))

    if real_inputs == 0: # ToDo
        continue

    r = solver.check()
    assert(str(r) == "sat")
    model = solver.model()
    current_solution = model.eval(expr)

    # get a different solution
    new_solution = current_solution
    input_new_values = input_values[:]
    solver = z3.Solver()
    solver.add(pi)

    input_indexes = []
    for input in inputs:
        index = int(str(input)[2:])
        if index >= len(input_values):
            continue
        input_indexes.append(index)
    for i in range(len(input_values)):
        if i not in input_indexes:
            input = z3.BitVec("k!%s" % i, 8)
            solver.add(input == input_values[i])
    solver.add(expr != current_solution)

    r = solver.check()
    if str(r) == "sat":
        model = solver.model()
        new_solution = model.eval(expr)
        for input in inputs:
            index = int(str(input)[2:])
            if index >= len(input_values):
                continue
            value = model.eval(input, model_completion=False)
            if type(value) == z3.BitVecNumRef:
                input_new_values[index] = value.as_long()

    # solver = z3.Solver()
    # solver.add(pi)
    # solver.add(expr == new_solution)
    # r = solver.check()
    # if str(r) == "sat":
    #     model = solver.model()
    #     print(model.eval(pi.arg(0)))
    #     print(model.eval(pi.arg(0).arg(1)))

    if new_solution == current_solution:
        if processed_queries % 1000 == 0:
            print("Processed %s debug queries" % processed_queries)
        # print("Cannot generate an alternative solution for the current expression Skipping it.")
        pass
    else:
        symbolic_queries += 1
        print("\n# [%d/%d] Analyzing debug query: %s" % (symbolic_queries, processed_queries, query.rstrip(".pi")))
        print("Path constraints: %s" % pi)
        print("Expression: %s" % expr)
        print("Inputs: %s" % inputs)
        print("Expression current value: %s" % current_solution)
        print("Expression new value: %s" % new_solution)

        # dump the new testcase
        assert len(input_values) == len(input_new_values)
        new_testcase = args.output_dir + "/.input"
        with open(new_testcase, "wb") as fp:
            for v in input_new_values:
                v = struct.pack("B", v)
                fp.write(v)

        # workdir
        workdir = args.output_dir + "/fuzz"
        if os.path.exists(workdir):
            safe_dir_rm(workdir)
        os.mkdir(workdir)
        os.system("touch %s/.fuzzolic_workdir" % workdir)

        # run the tracer
        env = os.environ.copy()
        env["DEBUG_FUZZ_EXPR_IDX"] = str(expr_idx)
        env["DEBUG_FUZZ_EXPR_VALUE"] = str(new_solution)

        p_args  = [ SCRIPT_DIR + "/fuzzolic.py"]
        p_args += [ "-i",  new_testcase ]
        p_args += [ "-o",  workdir ]
        p_args += [ "--fuzz-expr", "-l"]
        p_args += [ "--" ]
        p_args += [ args.binary ] + args.args

        # print(env["DEBUG_FUZZ_EXPR_IDX"])
        # print(env["DEBUG_FUZZ_EXPR_VALUE"])
        # print(' '.join(p_args))

        p = subprocess.Popen(
                            p_args,
                            #stdout=subprocess.DEVNULL,
                            #stderr=subprocess.DEVNULL,
                            env=env
                            )
        CHILDREN.append(p)
        p.wait()
        CHILDREN = []

        if p.returncode == 245:
            break

    i += 1
    #if i > 2000:
    #    break
