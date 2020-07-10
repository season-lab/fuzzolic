#!/usr/bin/python3 -u

import os
import sys
import subprocess
import argparse
import re

MODELS_LIBC = ["malloc", "free", "realloc", "calloc", "printf", "fprintf", "vfprintf"]
MODELS = [
    "strcmp",   # indirect call, offset in libc.so is not useful
    "strncmp",  # indirect call
    "strlen",   # indirect call
    "strnlen",  # indirect call
    "memchr",   # indirect call
    "memcmp",   # indirect call
    "memmove",  # indirect call
    "__printf_chk",
    "__memmove_chk",
    "memset",
    "__memset_chk",
    "memcpy",
    "__memcpy_chk",
    "strcpy",
    "strncpy"
]

def run(args):
    try:
        p = subprocess.Popen(args, stdout=subprocess.PIPE)
        data = p.communicate()
        stdout = str(data[0].decode('ascii'))
        return stdout
    except Exception as e:
        print("Error when running the program: %s" % e)
    return None


def process_plt_libc(binary, outfile=None):
    base_address = subprocess.check_output (
        "readelf -l %s | grep LOAD | head -n 1" % binary, shell=True )
    base_address = base_address.decode('ascii')
    base_address = int(list(filter(lambda x: x != '', base_address.split(" ")))[2], 16)
    try:
        res = subprocess.check_output (
            "nm -D %s" % binary, shell=True )
        res = res.decode('ascii')
        # print(res)
    except:
        res = ""
    for el in res.split("\n"):
        if el == "":
            continue
        split = el.split(" ")
        if len(split) != 3:
            continue
        addr = int(split[0], 16) - base_address
        name = split[2]
        type = split[1]
        if type not in ["T", "W"]:
            continue
        if name in MODELS_LIBC:
            if outfile is None:
                print("%s,%s,0x%x" % (os.path.basename(binary), name, addr))
            else:
                outfile.write("%s,%s,0x%x\n" % (os.path.basename(binary), name, addr))

def process_plt(binary, outfile=None):
    base_address = subprocess.check_output (
        "readelf -l %s | grep LOAD | head -n 1" % binary, shell=True )
    base_address = base_address.decode('ascii')
    base_address = int(list(filter(lambda x: x != '', base_address.split(" ")))[2], 16)
    try:
        res = subprocess.check_output (
            "objdump -d %s | grep \@plt\>\:" % binary, shell=True )
        res = res.decode('ascii')
    except:
        res = ""
    for el in res.split("\n"):
        if el == "":
            continue
        split = el.split(" ")
        addr = int(split[0], 16) - base_address
        name = split[1][1:split[1].find("@")]
        if name in MODELS:
            if outfile is None:
                print("%s,%s,0x%x" % (os.path.basename(binary), name, addr))
            else:
                outfile.write("%s,%s,0x%x\n" % (os.path.basename(binary), name, addr))

parser = argparse.ArgumentParser()
parser.add_argument('-o', '--output', metavar='<output>',
                        type=str, help='output path')
parser.add_argument('binary', metavar='<binary>',
                        type=str, help='path to the binary to run')

args = parser.parse_args()

if not os.path.exists(args.binary):
    print("Invalid binary: %s" % args.binary)
    sys.exit(1)

ldd_out = run(["ldd", args.binary])
ldd_out = ldd_out.strip("\t").split("\n")
libs = []
for lib in ldd_out:
    matches = re.findall(".* => (.+) \(.+\)", lib)
    for m in matches:
        if "libdl.so" not in m:
            libs.append(m)

outfile = None
if args.output:
    outfile = open(args.output, "w")

binaries = [ args.binary ] + libs
for b in binaries:
    if "libc.so" in b:
        process_plt_libc(b, outfile)
    else:
        process_plt(b, outfile)

if outfile:
    outfile.close()
