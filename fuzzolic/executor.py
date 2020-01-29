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


SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
SOLVER_BIN = SCRIPT_DIR + '/../solver/solver'
TRACER_BIN = SCRIPT_DIR + '/../tracer/x86_64-linux-user/qemu-x86_64'
SOLVER_WAIT_TIME_AT_STARTUP = 0.0005
SOLVER_TIMEOUT = 10
SHUTDOWN = False


class Executor(object):

    def __init__(self, binary, initial_seed, working_dir, binary_args, debug, delta_solving):

        if not os.path.exists(binary):
            sys.exit('ERROR: invalid binary')
        self.binary = binary
        self.binary_args = binary_args
        self.testcase_from_stdin = '@@' not in self.binary_args

        if not os.path.exists(working_dir):
            sys.exit('ERROR: invalid working directory')
        self.working_dir = os.path.abspath(working_dir)

        if not os.path.exists(initial_seed):
            sys.exit('ERROR: invalid initial seed')
        self.initial_seed = initial_seed

        self.debug = debug
        self.delta_solving = delta_solving

        self.__load_config()
        self.__warning_log = set()

    def __load_config(self):
        config = {}
        if not os.path.exists(self.binary + '.fuzzolic'):
            sys.exit('Configuration file for %s is missing' % self.binary)
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
        # root dir
        root_dir = self.working_dir + '/workdir'
        if not os.path.exists(root_dir):
            os.system('mkdir ' + root_dir)
        return root_dir

    def __get_queue_dir(self):
        queue_dir = self.__get_root_dir() + '/queue'
        if not os.path.exists(queue_dir):
            os.system('mkdir ' + queue_dir)
        return queue_dir

    def __get_test_cases_dir(self):
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
        if os.path.exists(run_dir):
            os.system('echo rm -rf ' + run_dir)
        os.system('mkdir ' + run_dir)

        # increment id for the next run
        with open(status_file, 'w') as sf:
            sf.write(str(run_id + 1))

        return run_dir, run_id

    def fuzz_one(self, testcase):

        self.__check_shutdown_flag()

        run_dir, run_id = self.__get_run_dir()
        print('\nRunning using testcase: %s' % testcase)
        print('Running directory: %s' % run_dir)

        env = os.environ.copy()
        for c in self.config:
            env[c] = self.config[c]
        if not self.testcase_from_stdin:
            env['SYMBOLIC_TESTCASE_NAME'] = testcase

        self.__check_shutdown_flag()

        p_solver_log_name = run_dir + '/solver.log'
        p_solver_log = open(p_solver_log_name, 'w')

        # launch solver
        if self.debug != 'no_solver':
            p_solver_args = []
            p_solver_args += ['stdbuf', '-o0']  # No buffering on stdout
            p_solver_args += [SOLVER_BIN]
            p_solver_args += [testcase]
            p_solver_args += [self.__get_test_cases_dir()]
            if self.delta_solving:
                p_solver_args += ['-d']
            p_solver = subprocess.Popen(p_solver_args,
                                        stdout=p_solver_log if not self.debug else None,
                                        stderr=subprocess.STDOUT if not self.debug else None,
                                        cwd=run_dir,
                                        env=env)

            # wait a few moments to let the solver setup setup shared memories
            time.sleep(SOLVER_WAIT_TIME_AT_STARTUP)

        # launch tracer
        p_tracer_log_name = run_dir + '/tracer.log'
        p_tracer_log = open(p_tracer_log_name, 'w')
        p_tracer_args = []

        if self.debug != 'gdb':
            p_tracer_args += ['stdbuf', '-o0']  # No buffering on stdout
            #p_tracer_args += ['strace']
        else:
            p_tracer_args += ['gdb']

        p_tracer_args += [TRACER_BIN]

        if self.debug != 'gdb':
            p_tracer_args += ['-symbolic']
            if self.debug == 'trace':
                p_tracer_args += ['-d']
                p_tracer_args += ['in_asm,op_opt,out_asm']  # 'in_asm,op_opt,out_asm'

        args = self.binary_args
        if not self.testcase_from_stdin:
            for k in range(len(args)):
                if args[k] == '@@':
                    args[k] = testcase

        if self.debug != 'gdb':
            p_tracer_args += [self.working_dir + '/' + self.binary]
            p_tracer_args += args

        p_tracer = subprocess.Popen(p_tracer_args,
                                    stdout=p_tracer_log if not self.debug else None,
                                    stderr=subprocess.STDOUT if not self.debug else None,
                                    stdin=subprocess.PIPE if self.testcase_from_stdin or self.debug == 'gdb' else None,
                                    cwd=run_dir,
                                    env=env,
                                    bufsize=0 if self.debug == 'gdb' else -1,
                                    #universal_newlines=True if self.debug == 'gdb' else False
                                    )

        # emit testcate on stdin
        if self.debug != 'gdb':
            if self.testcase_from_stdin:
                with open(testcase, "rb") as f:
                    p_tracer.stdin.write(f.read())
                    p_tracer.stdin.close()
        else:
            gdb_cmd = 'run -symbolic ' + self.working_dir + \
                '/' + self.binary + ' ' + ' '.join(args)
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
        p_tracer_log.close()

        if p_tracer.returncode != 0:
            returncode_str = "(SIGSEGV)" if p_tracer.returncode == -11 else ""
            print("ERROR: tracer has returned code %d %s" %
                  (p_tracer.returncode, returncode_str))
            if self.debug != 'no_solver':
                p_solver.send_signal(signal.SIGINT)

        p_solver.wait()
        """
        if self.debug != 'no_solver':
            try:
                p_solver.wait(SOLVER_TIMEOUT)
            except subprocess.TimeoutExpired:
                p_solver.send_signal(signal.SIGINT)
                try:
                    p_solver.wait(SOLVER_TIMEOUT)
                except subprocess.TimeoutExpired:
                    print('Solver will be killed.')
                    p_solver.send_signal(signal.SIGKILL)
        """

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

        # remove test case from queue dir
        os.system('rm ' + testcase)

        # check new test cases
        files = list(filter(os.path.isfile, glob.glob(
            run_dir + "/test_case_*.dat")))
        files.sort(key=lambda x: os.path.getmtime(x))

        k = 0
        for t in files:

            # check whether this a duplicate test case
            discard = False
            known_tests = glob.glob(
                self.__get_test_cases_dir() + "/test_case_*.dat")
            for kt in known_tests:
                if filecmp.cmp(kt, t):
                    print('Discarding %s since it is a duplicate' % t)
                    discard = True
                    break

            if not discard:
                print("Importing %s" % t)
                self.__import_test_case(
                    t, 'test_case_' + str(run_id) + '_' + str(k) + '.dat')
                k += 1

    def __import_test_case(self, testcase, name):
        os.system('cp ' + testcase + ' ' + self.__get_queue_dir() + '/' + name)
        os.system('cp ' + testcase + ' ' +
                  self.__get_test_cases_dir() + '/' + name)
        return self.__get_queue_dir() + '/' + name

    def __pick_testcase(self, initial_run=False):
        queued_inputs = list(
            filter(os.path.isfile, glob.glob(self.__get_queue_dir() + "/*")))

        if len(queued_inputs) == 0:

            if not initial_run:
                return None

            # copy the initial seed in the queue
            test_case_path = self.__import_test_case(
                self.working_dir + '/' + self.initial_seed, 'seed.dat')
            queued_inputs.append(test_case_path)

        elif len(queued_inputs) > 1:
            # sort the queue
            queued_inputs.sort(key=lambda x: os.path.getmtime(x))

        return queued_inputs[0]

    def __check_shutdown_flag(self):
        if SHUTDOWN:
            sys.exit("Forcefully terminating...")

    def run(self):

        self.__check_shutdown_flag()
        testcase = self.__pick_testcase(True)
        while testcase:
            self.fuzz_one(testcase)
            if self.debug:
                return
            self.__check_shutdown_flag()
            testcase = self.__pick_testcase()
            self.__check_shutdown_flag()

        for w in self.__warning_log:
            print(w)
