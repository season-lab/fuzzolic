#!/usr/bin/python2.7

import os
import sys
import json
import glob
import filecmp

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))


class Executor(object):

    def __init__(self, binary, initial_seed, working_dir):

        if not os.path.exists(binary):
            print 'ERROR: invalid binary.'
            sys.exit(1)
        self.binary = binary

        if not os.path.exists(working_dir):
            print 'ERROR: invalid working directory.'
            sys.exit(1)
        self.working_dir = os.path.abspath(working_dir)

        if not os.path.exists(initial_seed):
            print 'ERROR: invalid initial seed.'
            sys.exit(1)
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
            print 'Configuration file for ' + self.binary + ' is missing.'
            sys.exit(1)
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

        run_dir, run_id = self.__get_run_dir()
        print '\nRunning using testcase: ' + testcase
        print 'Running directory: ' + run_dir

        cmd = '('

        for c in self.config:
            cmd += 'export ' + c + '=' + self.config[c] + '; '
        cmd += 'env | grep SYMBOLIC >' + run_dir + '/tracer.log 2>&1; '

        # launch solver
        cmd += 'cd ' + run_dir + ' && '
        cmd += SCRIPT_DIR + '/../solver/solver'
        cmd += ' >' + run_dir + '/solver.log 2>&1 &'

        # launch tracer
        cmd += 'cd ' + run_dir + ' && '

        if self.config['SYMBOLIC_INJECT_INPUT_MODE'] == 'READ_FD_0':
            cmd += 'cat ' + testcase + ' | '

        cmd += ' ' + SCRIPT_DIR + \
            '/../tracer/x86_64-linux-user/qemu-x86_64 -symbolic ' + self.working_dir \
            + '/' + self.binary

        if self.config['SYMBOLIC_INJECT_INPUT_MODE'] == 'REG' \
                or self.config['SYMBOLIC_INJECT_INPUT_MODE'] == 'BUFFER':
            cmd += ' ' + testcase

        cmd += ' >' + run_dir + '/tracer.log 2>&1'

        cmd += ' && wait'
        cmd += ')'

        # run it
        os.system(cmd)

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
            known_tests = glob.glob(self.__get_test_cases_dir() + "/test_case_*.dat")
            for kt in known_tests:
                if filecmp.cmp(kt, t):
                    print "Discarding " + t + ' since it is a duplicate'
                    discard = True
                    break

            if not discard:
                print "Importing " + t
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

    def run(self):

        testcase = self.__pick_testcase(True)
        while testcase:
            self.fuzz_one(testcase)
            testcase = self.__pick_testcase()
