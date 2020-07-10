#!/usr/bin/env python3

"""
This is taken from QSYM
"""

import atexit
import os
import subprocess as sp
import tempfile
import copy
import struct
import hashlib
import os
import glob

SCRIPT_DIR = os.path.dirname(os.path.realpath(__file__))

# status for TestCaseMinimizer
NEW = 0
OLD = 1
CRASH = 2

TIMEOUT = 5 * 1000
MAP_SIZE = 65536
AT_FILE = "@@"

def get_hash(file):
    with open(file, "rb") as f:
        file_hash = hashlib.blake2b()
        chunk = f.read(8192)
        while chunk:
            file_hash.update(chunk)
            chunk = f.read(8192)
        return file_hash.hexdigest()
    return None

def get_score(testcase):
    # New coverage is the best
    score1 = testcase.endswith("+cov")
    # NOTE: seed files are not marked with "+cov"
    # even though it contains new coverage
    score2 = "orig:" in testcase
    # Smaller size is better
    score3 = -os.path.getsize(testcase)
    # Since name contains id, so later generated one will be chosen earlier
    score4 = testcase
    return (score1, score2, score3, score4)

def testcase_compare(a, b):
    a_score = get_score(a)
    b_score = get_score(b)
    return 1 if a_score > b_score else -1

def read_bitmap_file(bitmap_file):
    b = []
    with open(bitmap_file, "rb") as f:
        byte = f.read(1)
        while byte:
            b.append(struct.unpack('B', byte)[0])
            byte = f.read(1)
    return b

def write_bitmap_file(bitmap_file, bitmap):
    with open(bitmap_file, "wb") as f:
        for b in bitmap:
            f.write(struct.pack('B', b))

def fix_at_file(cmd, testcase):
    cmd = copy.copy(cmd)
    if AT_FILE in cmd:
        idx = cmd.index(AT_FILE)
        cmd[idx] = testcase
        stdin = None
    else:
        with open(testcase, "rb") as f:
            stdin = f.read()

    return cmd, stdin

class TestcaseMinimizer(object):
    def __init__(self, cmd, afl_path, out_dir, qemu_mode, fixed_name, map_size=MAP_SIZE):
        self.cmd = cmd
        self.qemu_mode = qemu_mode
        self.showmap = os.path.join(afl_path, "afl-showmap")
        self.showmap_fork = os.path.join(SCRIPT_DIR, "../utils/afl-showmap")
        self.bitmap_file = os.path.join(out_dir, "afl-bitmap")
        self.crash_bitmap_file = os.path.join(out_dir, "afl-crash-bitmap")
        _, self.temp_file = tempfile.mkstemp(dir=out_dir)
        atexit.register(self.cleanup)

        self.map_size = map_size
        self.bitmap = self.initialize_bitmap(self.bitmap_file, map_size)
        self.crash_bitmap = self.initialize_bitmap(self.crash_bitmap_file, map_size)
        self.hash_files = set()
        self.fixed_name = fixed_name

    def initialize_bitmap(self, filename, map_size):
        if os.path.exists(filename):
            print("Importing existing bitmap for minimizer")
            bitmap = read_bitmap_file(filename)
            assert len(bitmap) == map_size
        else:
            print("Initializing bitmap for minimizer")
            bitmap = [0] * map_size
        return bitmap

    def check_testcases(self, directory, global_bitmap_pre_run=None, no_msg=False):
        res = {}
        with tempfile.TemporaryDirectory() as tmpdir:
            cmd = [self.showmap_fork,
                "-t",
                str(TIMEOUT),
                "-m", "16G",
                "-b" # binary mode
            ]

            if self.qemu_mode:
                cmd += ['-Q']

            cmd += ["-o",
                tmpdir,
                '-i',
                directory,
                "--",
            ] + self.cmd

            env = os.environ.copy()
            # env["AFL_INST_LIBS"] = "1"

            with open(os.devnull, "wb") as devnull:
                proc = sp.Popen(cmd, stdin=None, stdout=devnull, stderr=devnull, env=env)
                proc.wait()

            for f in glob.glob(tmpdir + "/*.dat"):

                #this_bitmap = read_bitmap_file(f)
                #interesting = self.is_interesting_testcase(this_bitmap, proc.returncode)
                interesting = self.is_interesting_testcase_fork(f)
                res[os.path.basename(f)] = interesting

                if not no_msg:
                    if interesting:
                        print("[+] Keeping %s" % os.path.basename(f))
                    else:
                        print("[-] Discarding %s" % os.path.basename(f))
        return res

    def check_testcase(self, testcase, global_bitmap_pre_run=None, no_msg=False):

        """
        hash = get_hash(testcase)
        assert hash is not None
        print("Hash is %s"  % hash)
        if hash in self.hash_files:
            print("Duplicate testcase")
            return False
        self.hash_files.add(hash)
        """

        cmd = [self.showmap,
               "-t",
               str(TIMEOUT),
               "-m", "16G",
               "-b" # binary mode
        ]

        if self.qemu_mode:
            cmd += ['-Q']

        cmd += ["-o",
               self.temp_file,
               "--"
        ] + self.cmd

        env = os.environ.copy()
        # env["AFL_INST_LIBS"] = "1"

        input = testcase
        if self.fixed_name:
            with tempfile.TemporaryDirectory() as tmpdir:
                new_input = "%s/%s" % (tmpdir, self.fixed_name)
                os.system("cp %s %s" % (testcase, new_input))
                input = new_input
                cmd, stdin = fix_at_file(cmd, input)
                # print(cmd)
                with open(os.devnull, "wb") as devnull:
                    proc = sp.Popen(cmd, stdin=sp.PIPE, stdout=devnull, stderr=devnull, env=env)
                    proc.communicate(stdin)
        else:
            cmd, stdin = fix_at_file(cmd, input)
            with open(os.devnull, "wb") as devnull:
                proc = sp.Popen(cmd, stdin=sp.PIPE, stdout=devnull, stderr=devnull, env=env)
                proc.communicate(stdin)

        this_bitmap = read_bitmap_file(self.temp_file)
        interesting = self.is_interesting_testcase(this_bitmap, proc.returncode)

        if not no_msg:
            if interesting:
                print("[+] Keeping %s" % os.path.basename(testcase))
            else:
                print("[-] Discarding %s" % os.path.basename(testcase))

        return interesting

    def is_interesting_testcase_fork(self, bitmap):
        my_bitmap_file = self.bitmap_file

        cmd = [
            SCRIPT_DIR + '/../utils/merge_bitmap',
            bitmap,
            my_bitmap_file
        ]
        # print(cmd)

        with open(os.devnull, "wb") as devnull:
            proc = sp.Popen(cmd, stdin=None, stdout=devnull, stderr=devnull)
            proc.wait()
            if proc.returncode == 0:
                return True
            elif proc.returncode == 2:
                return False
            else:
                print("Error while merging bitmap %s [error code %d]" % (bitmap, proc.returncode))
                return False

        print("Error while merging bitmap %s" % bitmap)
        return False

    def is_interesting_testcase(self, bitmap, returncode):
        if returncode == 0:
            my_bitmap = self.bitmap
            my_bitmap_file = self.bitmap_file
        else:
            my_bitmap = self.crash_bitmap
            my_bitmap_file = self.crash_bitmap_file

        # Maybe need to port in C to speed up
        interesting = False
        for i in range(self.map_size):
            old = my_bitmap[i]
            new = my_bitmap[i] | bitmap[i]
            if old != new:
                interesting = True
                my_bitmap[i] = new

        if interesting:
            write_bitmap_file(my_bitmap_file, my_bitmap)

        return interesting

    def cleanup(self):
        os.unlink(self.temp_file)
