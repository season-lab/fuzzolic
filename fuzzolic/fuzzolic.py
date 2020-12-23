#!/usr/bin/python3 -u

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
    # print(executor.RUNNING_PROCESSES)
    for p in executor.RUNNING_PROCESSES:
        print("[FUZZOLIC] Sending SIGINT")
        p.send_signal(signal.SIGINT)
        p.send_signal(signal.SIGUSR2)
        try:
            p.wait(2)
            try:
                executor.RUNNING_PROCESSES.remove(p)
            except:
                pass
        except:
            print("[FUZZOLIC] Sending SIGKILL")
            p.send_signal(signal.SIGKILL)
            try:
                executor.RUNNING_PROCESSES.remove(p)
            except:
                pass
            p.wait()

    # if len(executor.RUNNING_PROCESSES) == 0:
    #    sys.exit(1)

    global ABORTING_COUNT
    ABORTING_COUNT += 1
    if ABORTING_COUNT >= 3:
       sys.exit("Killing fuzzolic without cleanup. Not good.")


def main():

    parser = argparse.ArgumentParser(
        description='fuzzing + concolic = fuzzolic :)')

    # version
    parser.add_argument('--version', action='version',
                        version='%(prog)s pre-{\\alpha}^{\infty}')

    # optional args
    parser.add_argument(
        '-d', '--debug', choices=['coverage', 'gdb_trace', 'trace', 'out', 'no_solver', 'gdb_solver'], help='enable debug mode')
    parser.add_argument(
        '-a', '--afl', help='path to afl workdir (it enables AFL mode); AFL_PATH must be set.')
    parser.add_argument(
        '-t', '--timeout', type=int, help='set timeout on the solving time (ms)')
    parser.add_argument(
        '-f', '--fuzzy', action='store_true', help='use fuzzy solver')
    parser.add_argument(
        '-m', '--mixed', action='store_true', help='use fuzzy solver, then Z3 when empty queue [experimental]')
    parser.add_argument(
        '-r', '--address-reasoning', action='store_true', help='enable address reasoning')
    parser.add_argument(
        '-s', '--memory-slice', action='store_true', help='enable memory slice reasoning [experimental]')
    parser.add_argument(
        '-p', '--optimistic-solving', action='store_true', help='enable optimistic solving')
    parser.add_argument(
        '-n', '--input-fixed-name', help='Input name to use for input files [experimental]')
    parser.add_argument(
        '-l', '--symbolic-models', action='store_true', help='Enable symbolic models')
    parser.add_argument(
        '--fuzz-expr', action='store_true', help='enable fuzz expression (debug) [experimental]')
    parser.add_argument(
        '-k', '--keep-run-dirs', action='store_true', help='keep run directories')
    parser.add_argument(
        '--single-path', action='store_true', help='perform a single-path exploration (first input from the input directory)')

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

    fuzzy = args.fuzzy
    use_smt_if_empty = False
    if args.mixed:
        fuzzy = True
        use_smt_if_empty = True

    timeout = args.timeout
    if timeout is None:
        timeout = 0
    optimistic_solving = args.optimistic_solving
    if optimistic_solving is None:
        optimistic_solving = False
    address_reasoning = args.address_reasoning
    if address_reasoning is None:
        address_reasoning = False
    memory_slice_reasoning = args.memory_slice
    if memory_slice_reasoning is None:
        memory_slice_reasoning = False
    fuzz_expr = args.fuzz_expr
    if fuzz_expr is None:
        fuzz_expr = False
    input_fixed_name = args.input_fixed_name
    symbolic_models = args.symbolic_models
    if symbolic_models is None:
        symbolic_models = False
    keep_run_dirs = args.keep_run_dirs
    if keep_run_dirs is None:
        keep_run_dirs = False
    single_path = args.single_path
    if single_path is None:
        single_path = False
    if debug is not None:
        print("WARNING: in debug mode, only a single path is explored.")
        single_path = True

    signal.signal(signal.SIGINT, handler)

    fuzzolic_executor = executor.Executor(
        binary, input, output_dir, binary_args, debug, afl,
        timeout, fuzzy, optimistic_solving, memory_slice_reasoning,
        address_reasoning, fuzz_expr, input_fixed_name, use_smt_if_empty,
        symbolic_models, keep_run_dirs, single_path)
    fuzzolic_executor.run()


if __name__ == "__main__":
    main()
