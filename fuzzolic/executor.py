#!/usr/bin/python3

import os
import sys
import json
import glob
import filecmp
import subprocess
import time
import signal
import configparser
import re
import shutil
import functools
import tempfile

import minimizer_qsym
import minimizer

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
SOLVER_BIN = SCRIPT_DIR + '/../solver/solver'
TRACER_BIN = SCRIPT_DIR + '/../tracer/x86_64-linux-user/qemu-x86_64'
AFL_PATH = SCRIPT_DIR + '/../../AFL/'

SOLVER_WAIT_TIME_AT_STARTUP = 0.0010
SOLVER_TIMEOUT = 10
SHUTDOWN = False

class Executor(object):

    def __init__(self, binary, input, output_dir, binary_args, debug=None, afl=None):

        if not os.path.exists(binary):
            sys.exit('ERROR: invalid binary')
        self.binary = os.path.abspath(binary)

        self.binary_args = binary_args
        self.testcase_from_stdin = '@@' not in self.binary_args

        if not os.path.exists(output_dir):
            sys.exit('ERROR: invalid working directory')
        self.output_dir = os.path.abspath(output_dir)

        if not os.path.exists(input):
            sys.exit('ERROR: invalid input')
        self.input = os.path.abspath(input)

        self.global_bitmap = self.__get_root_dir() + '/branch_bitmap'
        os.system("touch " + self.global_bitmap)

        if afl:
            if not os.path.exists(afl):
                sys.exit('ERROR: invalid AFL workdir')
            self.afl = os.path.abspath(afl)
            self.minimizer = minimizer_qsym.TestcaseMinimizer([binary] + binary_args, AFL_PATH, output_dir, True)
            # self.minimizer = minimizer.TestcaseMinimizer([binary] + binary_args, self.global_bitmap)
        else:
            self.afl = None
            self.minimizer = minimizer_qsym.TestcaseMinimizer([binary] + binary_args, AFL_PATH, output_dir, True)
            # self.minimizer = minimizer.TestcaseMinimizer([binary] + binary_args, self.global_bitmap)
        self.afl_processed_testcases = set()

        self.debug = debug
        self.tick_count = 0

        self.__load_config()
        self.__warning_log = set()

    def __load_config(self):
        config = {}
        if not os.path.exists(self.binary + '.fuzzolic'):
            print('Configuration file for %s is missing. Using default configuration.' % self.binary)
            config['SYMBOLIC_INJECT_INPUT_MODE'] = "FROM_FILE"
        else:
            with open(self.binary + '.fuzzolic', 'r') as cfgfile:
                for line in cfgfile:
                    line = line.rstrip('\n').strip()
                    if line.startswith('#') or '=' not in line:
                        continue
                    pivot = line.index('=')
                    key = line[:pivot]
                    value = line[pivot + 1:]
                    config[key] = value
        self.config = config

    def __get_root_dir(self):
        if not os.path.exists(self.output_dir):
            os.system('mkdir ' + self.output_dir)
        return self.output_dir

    def __get_queue_dir(self):
        queue_dir = self.__get_root_dir() + '/queue'
        if not os.path.exists(queue_dir):
            os.system('mkdir ' + queue_dir)
        return queue_dir

    def __get_testcases_dir(self):
        testcases_dir = self.__get_root_dir() + '/tests'
        if not os.path.exists(testcases_dir):
            os.system('mkdir ' + testcases_dir)
        return testcases_dir

    def __get_run_dir(self):
        root_dir = self.__get_root_dir()

        # status file
        status_file = root_dir + '/status'
        if not os.path.exists(status_file):
            os.system('echo 0 > ' + status_file)

        # get id for next run
        with open(status_file, 'r') as sf:
            run_id = sf.read()
            run_id = int(run_id)
            assert(run_id >= 0)

        # run dir
        run_dir = root_dir + '/fuzzolic-' + str(run_id)
        os.system('mkdir ' + run_dir)

        # increment id for the next run
        with open(status_file, 'w') as sf:
            sf.write(str(run_id + 1))

        return run_dir, run_id

    def fuzz_one(self, testcase, target):

        self.__check_shutdown_flag()

        run_dir, run_id = self.__get_run_dir()
        print('\nRunning using testcase: %s' % testcase)
        print('Running directory: %s' % run_dir)

        os.system("cp " + testcase + " " + run_dir)

        env = os.environ.copy()
        for c in self.config:
            env[c] = self.config[c]
        if not self.testcase_from_stdin:
            env['SYMBOLIC_TESTCASE_NAME'] = testcase

        if self.debug == 'coverage':
            env['COVERAGE_TRACER'] = self.output_dir + '/fuzzolic-bitmap'
            env['COVERAGE_TRACER_LOG'] = self.output_dir + '/fuzzolic-coverage.out'

        self.__check_shutdown_flag()

        _, global_bitmap_pre_run = tempfile.mkstemp()
        os.system("cp " + self.global_bitmap + " " + global_bitmap_pre_run)

        p_solver_log_name = run_dir + '/solver.log'
        p_solver_log = open(p_solver_log_name, 'w')

        gdb_solver = False

        # launch solver
        if self.debug != 'no_solver' and self.debug != 'coverage':
            p_solver_args = []
            p_solver_args += ['stdbuf', '-o0']  # No buffering on stdout
            p_solver_args += [SOLVER_BIN]
            p_solver_args += ['-i', testcase]
            p_solver_args += ['-t', self.__get_testcases_dir()]
            p_solver_args += ['-o', run_dir]

            p_solver_args += ['-b', self.global_bitmap]
            #p_solver_args += ['-b', os.path.join(self.output_dir, '/afl-bitmap')]

            p_solver_args += ['-c', self.__get_root_dir() + '/context_bitmap']
            p_solver_args += ['-m', self.__get_root_dir() + '/memory_bitmap']
            if not gdb_solver:
                p_solver = subprocess.Popen(p_solver_args,
                                        stdout=p_solver_log if not self.debug else None,
                                        stderr=subprocess.STDOUT if not self.debug else None,
                                        cwd=run_dir,
                                        env=env)
            else:
                p_solver = subprocess.Popen(['gdb'] + p_solver_args[0:1],
                                        stdout=p_solver_log if not self.debug else None,
                                        stderr=subprocess.STDOUT if not self.debug else None,
                                        stdin=subprocess.PIPE,
                                        cwd=run_dir,
                                        bufsize=0,
                                        env=env)

                gdb_cmd = 'run ' + ' '.join(p_solver_args[1:])
                gdb_cmd += "\n"
                try:
                    p_solver.wait(5)
                except:
                    pass
                print("GDB command: %s" % gdb_cmd)
                p_solver.stdin.write("break set_add__index_group_t\n".encode())
                p_solver.stdin.write(gdb_cmd.encode())
                # p_solver.stdin.close()

            # wait a few moments to let the solver setup setup shared memories
            time.sleep(SOLVER_WAIT_TIME_AT_STARTUP)

        if gdb_solver:
            time.sleep(10)

        # launch tracer
        p_tracer_log_name = run_dir + '/tracer.log'
        p_tracer_log = open(p_tracer_log_name, 'w')

        p_tracer_args = []
        if self.debug != 'gdb':
            p_tracer_args += ['stdbuf', '-o0']  # No buffering on stdout
        else:
            p_tracer_args += ['gdb']

        p_tracer_args += [TRACER_BIN]

        if self.debug != 'gdb':
            p_tracer_args += ['-symbolic']
            if self.debug == 'trace':# or self.debug == 'no_solver':
                p_tracer_args += ['-d']
                p_tracer_args += ['in_asm,op_opt,out_asm']  # 'in_asm,op_opt,out_asm'

        args = self.binary_args
        if not self.testcase_from_stdin:
            for k in range(len(args)):
                if args[k] == '@@':
                    args[k] = testcase

        if self.debug != 'gdb':
            p_tracer_args += [self.binary]
            p_tracer_args += args

        # print(p_tracer_args)

        p_tracer = subprocess.Popen(p_tracer_args,
                                    stdout=p_tracer_log if not self.debug else None,
                                    stderr=subprocess.STDOUT if not self.debug else None,
                                    stdin=subprocess.PIPE if self.testcase_from_stdin or self.debug == 'gdb' else None,
                                    cwd=run_dir,
                                    env=env,
                                    bufsize=0 if self.debug == 'gdb' else -1,
                                    #universal_newlines=True if self.debug == 'gdb' else False
                                    )

        # print("Tracer started")

        # emit testcate on stdin
        if self.debug != 'gdb':
            if self.testcase_from_stdin:
                with open(testcase, "rb") as f:
                    p_tracer.stdin.write(f.read())
                    p_tracer.stdin.close()
        else:
            gdb_cmd = 'run -d in_asm,op,op_opt,out_asm -symbolic ' + self.binary + ' ' + ' '.join(args)
            if self.testcase_from_stdin:
                gdb_cmd += ' < ' + testcase
            gdb_cmd += "\n"
            print("GDB command: %s" % gdb_cmd)
            p_tracer.stdin.write(gdb_cmd.encode())
            for line in sys.stdin:
                #print("Sending to gdb: " + line)
                p_tracer.stdin.write(line.encode())
                if 'quit' in line or line.startswith('q'):
                    print("Closing stdin in gdb")
                    break
            p_tracer.stdin.close()

        p_tracer.wait()
        # print("Tracer completed")
        p_tracer_log.close()

        if gdb_solver:
            for line in sys.stdin:
                p_solver.stdin.write(line.encode())
                if 'quit' in line or line.startswith('q'):
                    print("Closing stdin in gdb")
                    break
            p_solver.stdin.close()

        if p_tracer.returncode != 0:
            returncode_str = "(SIGSEGV)" if p_tracer.returncode == -11 else ""
            print("ERROR: tracer has returned code %d %s" %
                  (p_tracer.returncode, returncode_str))
            if self.debug != 'no_solver' and self.debug != 'coverage':
                p_solver.send_signal(signal.SIGINT)
                time.sleep(2)
                p_solver.send_signal(signal.SIGKILL)

        if self.debug != 'no_solver' and self.debug != 'coverage':
            while not SHUTDOWN:
                try:
                    p_solver.wait(SOLVER_TIMEOUT)
                    break
                except subprocess.TimeoutExpired:
                    pass

            if SHUTDOWN:
                p_solver.send_signal(signal.SIGINT)
                try:
                    p_solver.wait(SOLVER_TIMEOUT)
                except subprocess.TimeoutExpired:
                    print('Solver will be killed.')
                    p_solver.send_signal(signal.SIGKILL)

        p_solver_log.close()

        # parse tracer logs for known errors/warnings
        if not self.debug:
            with open(p_tracer_log_name, 'r') as log:
                for line in log:
                    #if re.search('Helper', line):
                    if 'Unhandled TCG instruction' in line or 'Helper ' in line:
                        if line not in self.__warning_log:
                            self.__warning_log.add("[tracer warning]: %s" % line)

            with open(p_solver_log_name, 'r') as log:
                for line in log:
                    if 'PROGRAM ABORT' in line:
                        if line not in self.__warning_log:
                            self.__warning_log.add("[solver warning]: %s" % line)

        # check new test cases
        files = list(filter(os.path.isfile, glob.glob(
            run_dir + "/test_case_*.dat")))
        files.sort(key=lambda x: os.path.getmtime(x))
        k = 0
        for t in files:
            if self.afl:
                good = self.__check_testcase_afl(t, run_id, k, target, global_bitmap_pre_run)
            else:
                good = self.__check_testcase(t, run_id, k, target, global_bitmap_pre_run)
                # good = self.__check_testcase_full(t, run_id, k, target)
            if good:
                k += 1

        os.unlink(global_bitmap_pre_run)

    def __check_testcase(self, t, run_id, k, target, global_bitmap_pre_run):

        if self.minimizer.check_testcase(t, global_bitmap_pre_run):
            self.__import_test_case(
                t, 'test_case_' + str(run_id) + '_' + str(k) + '.dat')
            return True
        else:
            return False

    def __check_testcase_full(self, t, run_id, k, target):
        # check whether this a duplicate test case
        discard = False
        known_tests = glob.glob(
            self.__get_testcases_dir() + "/*.dat")
        for kt in known_tests:
            if filecmp.cmp(kt, t, shallow=False):
                print('Discarding %s since it is a duplicate (%s)' % (t, kt))
                discard = True
                break

        if not discard:
            print("Importing %s with id=%s_%s" % (t, run_id, k))
            self.__import_test_case(
                t, 'test_case_' + str(run_id) + '_' + str(k) + '.dat')

        return not discard

    def tick(self):
        self.tick_count += 1
        return self.tick_count - 1

    def __check_testcase_afl(self, t, run_id, k, target, global_bitmap_pre_run = None):
        if self.minimizer.check_testcase(t, global_bitmap_pre_run):
            # print("Importing %s" % t)
            target = os.path.basename(target)[:len("id:......")]
            name = "id:%06d,src:%s" % (self.tick(), target)
            self.__import_test_case(t, name)
            return True
        else:
            # print('Discarding %s since it is not interesting.' % t)
            return False

    def __import_test_case(self, testcase, name):
        os.system('cp ' + testcase + ' ' + self.__get_queue_dir() + '/' + name)
        os.system('cp ' + testcase + ' ' +
                  self.__get_testcases_dir() + '/' + name)
        return self.__get_queue_dir() + '/' + name

    @property
    def cur_input(self):
        return self.__get_root_dir() + '/.input'

    def __pick_testcase(self, initial_run=False):

        if self.afl:
            queued_inputs = self.__import_from_afl()
            waiting_rounds = 0
            while len(queued_inputs) == 0:
                waiting_rounds += 1
                time.sleep(0.1)
                queued_inputs = self.__import_from_afl()

            if waiting_rounds > 0:
                print("\nWaited %s seconds for a new input from AFL\n" % (waiting_rounds * 0.1))

            self.afl_processed_testcases.add(queued_inputs[0])
            shutil.copy2(queued_inputs[0], self.cur_input)

            #if initial_run:
            # update bitmap
            self.minimizer.check_testcase(self.cur_input, self.global_bitmap, True)

            return self.cur_input, os.path.basename(queued_inputs[0])

        else:
            queued_inputs = list(
                filter(os.path.isfile, glob.glob(self.__get_queue_dir() + "/*")))

            if len(queued_inputs) == 0:
                if not initial_run:
                    return None, None

                # copy the initial seed(s) in the queue
                if not os.path.isdir(self.input):
                    test_case_path = self.__import_test_case(self.input, 'seed.dat')
                    queued_inputs.append(test_case_path)
                else:
                    for t in glob.glob(self.input + '/*'):
                        test_case_path = self.__import_test_case(t, os.path.basename(t))
                        queued_inputs.append(test_case_path)

                self.minimizer.check_testcase(queued_inputs[0], self.global_bitmap, True)

            elif len(queued_inputs) > 1:
                # sort the queue
                queued_inputs.sort(key=lambda x: os.path.getmtime(x))

            shutil.copy2(queued_inputs[0], self.cur_input)

            # remove from the queue
            os.unlink(queued_inputs[0])

            return self.cur_input, os.path.basename(queued_inputs[0])

    def __check_shutdown_flag(self):
        if SHUTDOWN:
            sys.exit("Forcefully terminating...")

    def __import_from_afl(self):
        if not self.afl:
            return []

        afl_queue = self.afl + '/queue/'
        files = []
        for name in os.listdir(afl_queue):
            path = os.path.join(afl_queue, name)
            if os.path.isfile(path):
                files.append(path)

        files = list(set(files) - self.afl_processed_testcases)
        return sorted(files,
                      key=functools.cmp_to_key(minimizer_qsym.testcase_compare),
                      reverse=True)

    def run(self):

        self.__check_shutdown_flag()
        testcase, target = self.__pick_testcase(True)
        while testcase:
            start = time.time()
            self.fuzz_one(testcase, target)
            end = time.time()
            print("Run took %s secs" % (end-start))
            if self.debug:
                return
            self.__check_shutdown_flag()
            testcase, target = self.__pick_testcase()
            self.__check_shutdown_flag()

        print("[FUZZOLIC] no more testcase. Finishing.")

        if len(self.__warning_log):
            print()
        for w in self.__warning_log:
            print(w)
