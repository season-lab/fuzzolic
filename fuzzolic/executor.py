#!/usr/bin/python3

import os
import sys
import json
import glob
import filecmp
import subprocess
import time
import signal


SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))
SOLVER_BIN = SCRIPT_DIR + '/../solver/solver'
TRACER_BIN = SCRIPT_DIR + '/../tracer/x86_64-linux-user/qemu-x86_64'
SOLVER_WAIT_TIME_AT_STARTUP = 0.0005
SOLVER_TIMEOUT = 10
SHUTDOWN = False


class Executor(object):

    def __init__(self, binary, initial_seed, working_dir):

        if not os.path.exists(binary):
            sys.exit('ERROR: invalid binary')
        self.binary = binary

        if not os.path.exists(working_dir):
            sys.exit('ERROR: invalid working directory')
        self.working_dir = os.path.abspath(working_dir)

        if not os.path.exists(initial_seed):
            sys.exit('ERROR: invalid initial seed')
        self.initial_seed = initial_seed

        self.__load_config()

    def __get_config_str(self, data, key, config):
        if key in data:
            addr = data[key]
            config[key] = addr

    def __get_config_addr(self, data, key, config):
        if key in data:
            addr = data[key]
            addr = int(addr, 16)
            config[key] = addr

    def __load_config(self):
        config = {}
        if not os.path.exists(self.binary + '.json'):
            sys.exit('Configuration file for %s is missing' % self.binary)
        with open(self.binary + '.json', 'r') as cfgfile:
            data = json.load(cfgfile)
            self.__get_config_str(data, 'SYMBOLIC_EXEC_START_ADDR', config)
            self.__get_config_str(data, 'SYMBOLIC_EXEC_STOP_ADDR', config)
            self.__get_config_str(data, 'SYMBOLIC_INJECT_INPUT_MODE', config)
            self.__get_config_str(data, 'SYMBOLIC_EXEC_REG_NAME', config)
            self.__get_config_str(data, 'SYMBOLIC_EXEC_REG_INSTR_ADDR', config)
            self.__get_config_str(data, 'SYMBOLIC_EXEC_BUFFER_ADDR', config)
            self.__get_config_str(
                data, 'SYMBOLIC_EXEC_BUFFER_INSTR_ADDR', config)
        self.config = config

    def __get_root_dir(self):
        # root dir
        root_dir = self.working_dir + '/fuzzolic_working_dir'
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
            assert c not in env
            env[c] = self.config[c]

        self.__check_shutdown_flag()

        # launch solver
        p_solver_log = open(run_dir + '/solver.log', 'w')
        p_solver_args = [SOLVER_BIN]
        p_solver = subprocess.Popen(p_solver_args,
                                    stdout=p_solver_log,
                                    stderr=subprocess.STDOUT,
                                    cwd=run_dir,
                                    env=env)

        # wait a few moments to let the solver setup setup shared memories
        time.sleep(SOLVER_WAIT_TIME_AT_STARTUP)

        # launch tracer
        p_tracer_log = open(run_dir + '/tracer.log', 'w')
        p_tracer_args = [TRACER_BIN]
        p_tracer_args += ['-symbolic']
        p_tracer_args += [self.working_dir + '/' + self.binary]

        p_tracer = subprocess.Popen(p_tracer_args,
                                    stdout=p_tracer_log,
                                    stderr=subprocess.STDOUT,
                                    stdin=subprocess.PIPE,
                                    cwd=run_dir,
                                    env=env)

        # emit testcate on stdin
        if self.config['SYMBOLIC_INJECT_INPUT_MODE'] in ('READ_FD_0', 'REG', 'BUFFER'):
            with open(testcase, "rb") as f:
                p_tracer.stdin.write(f.read())
                p_tracer.stdin.close()

        p_tracer.wait()

        p_solver.wait(SOLVER_TIMEOUT)
        if p_solver.poll() is None:
            p_solver.send_signal(signal.SIGINT)
            p_solver.wait(SOLVER_TIMEOUT)
            if p_solver.poll() is None:
                print('Solver will be killed.')
                p_solver.send_signal(signal.SIGKILL)

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
            self.__check_shutdown_flag()
            testcase = self.__pick_testcase()
            self.__check_shutdown_flag()
