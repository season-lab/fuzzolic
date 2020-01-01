#!/usr/bin/python2.7

import os
import sys
import json

DIR = os.path.dirname(os.path.realpath(__file__))


def get_config_str(data, key, config):
    if key in data:
        addr = data[key]
        config[key] = addr


def get_config_addr(data, key, config):
    if key in data:
        addr = data[key]
        addr = int(addr, 16)
        config[key] = addr


def read_config(binary):
    config = {}
    if not os.path.exists(binary + '.json'):
        print 'Configuration file for ' + BINARY + ' is missing.'
        sys.exit(1)
    with open(binary + '.json', 'r') as cfgfile:
        data = json.load(cfgfile)
        get_config_str(data, 'SYMBOLIC_EXEC_START_ADDR', config)
        get_config_str(data, 'SYMBOLIC_EXEC_STOP_ADDR', config)
        get_config_str(data, 'SYMBOLIC_EXEC_REG_NAME', config)
        get_config_str(data, 'SYMBOLIC_EXEC_REG_ADDR', config)
    return config


def run(binary, conf):

    cmd = '('
    for c in config:
        cmd += 'export ' + c + '=' + config[c] + '; '
    cmd += 'env | grep SYMBOLIC; '

    cmd += DIR + '/../solver/solver &'
    cmd += ' ' + DIR + \
        '/../tracer/x86_64-linux-user/qemu-x86_64 -symbolic ' + binary
    cmd += ' && wait'
    cmd += ')'

    os.system(cmd)


if __name__ == "__main__":

    if len(sys.argv) != 2:
        print 'Usage: ' + sys.argv[0] + ' <binary>'
        sys.exit(1)

    binary = sys.argv[1]
    if not os.path.exists(binary):
        print 'ERROR: invalid binary'
        sys.exit(1)

    config = read_config(binary)
    run(binary, config)
