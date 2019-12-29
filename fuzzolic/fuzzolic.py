import os
import sys

if __name__ == "__main__":
    DIR = os.path.dirname(os.path.realpath(__file__))
    os.system(DIR + '/../solver/solver &')
    os.system(DIR + '/../tracer/x86_64-linux-user/qemu-x86_64 -symbolic ../tests/simple-if')